// Gimple Pass to recognize simple vector addition loops and replace them with calls to an external kaddv_complete helper.

#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "backend.h"
#include "tree.h"
#include "basic-block.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "tree-pass.h"
#include "tree-cfg.h"
#include "context.h"
#include "target.h"
#include "fold-const.h"
#include "riscv-protos.h"
#include "functional"
#include "cfgloopmanip.h"
#include "cfg.h"
#include "cfganal.h"
#include "cfgloop.h"
#include "cfghooks.h"
#include "tree-ssa-loop.h"   // expr_invariant_in_loop_p (if available)

namespace {

const pass_data pass_data_kaddv =
{
  GIMPLE_PASS, /* type */
  "kaddv_loop", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  PROP_gimple_any, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0 /* todo_flags_finish */
};

class pass_kaddv_loop : public gimple_opt_pass
{
public:
  pass_kaddv_loop(gcc::context *ctxt) : gimple_opt_pass(pass_data_kaddv, ctxt) {}

  bool gate(function *fun) override {
    if (!loops_for_fn(fun)) {
      fprintf(stderr, "gate: no loops for fn\n");
      return false;
    }
    return true;
  }
  unsigned int execute(function *fun) override;
};


// Strip i-dependent pieces from a pointer SSA: peel POINTER_PLUS, casts, etc.
static tree strip_pointer_iv (tree p) {
    for (;;) {
        if (TREE_CODE(p) == SSA_NAME) {
            gimple *def = SSA_NAME_DEF_STMT(p);
            if (!def || !is_gimple_assign(def)) break;
            enum tree_code c = gimple_assign_rhs_code(def);
            if (c == POINTER_PLUS_EXPR || c == NOP_EXPR || c == VIEW_CONVERT_EXPR) {
                p = gimple_assign_rhs1(def);
                continue;
            }
        }
        break;
    }
    return p;
}

static bool is_invariant_in_loop (struct loop *loop, tree t) {
    if (TREE_CODE(t) != SSA_NAME) return true;            // VAR_DECL, parm => invariant
    gimple *def = SSA_NAME_DEF_STMT(t);
    if (!def) return true;                                // should not happen, but ok
    basic_block bb = gimple_bb(def);
    return !flow_bb_inside_loop_p(loop, bb);
}

// Turn an ARRAY_REF or MEM_REF into a loop-invariant void* base pointer.
static tree make_base_ptr (struct loop *loop, tree ref) {
    if (TREE_CODE(ref) == ARRAY_REF) {
        // ref = base[i]; just take &base. No manual [0] construction.
        tree base = TREE_OPERAND(ref, 0);             // VAR_DECL or parm
        tree addr = build_fold_addr_expr(base);       // &base
        return fold_convert(ptr_type_node, addr);     // void*
    }
    if (TREE_CODE(ref) == MEM_REF) {
        tree p = strip_pointer_iv(TREE_OPERAND(ref, 0)); // try to drop i*stride
        // If still variant inside the loop, don’t use it in preheader.
        // (If expr_invariant_in_loop_p isn’t declared in your tree, just skip this check.)
        if (!is_invariant_in_loop(loop, p))
          return NULL_TREE;
        return fold_convert(ptr_type_node, p);
    }
    // Also allow passing through ADDR_EXPR(var) if you ever hand us one.
    if (TREE_CODE(ref) == ADDR_EXPR)
        return fold_convert(ptr_type_node, ref);
    return NULL_TREE;
}

// Find or create a preheader by splitting an incoming outside edge.
static basic_block get_or_make_preheader(struct loop *loop)
{
  basic_block header = loop->header;

  // Find a predecessor from *outside* the loop.
  edge outside_e = NULL;
  {
    edge e; edge_iterator ei;
    FOR_EACH_EDGE (e, ei, header->preds)
      if (!flow_bb_inside_loop_p (loop, e->src)) {
        outside_e = e;
        break;
      }
  }
  if (!outside_e)
    return NULL;  // No outside pred (degenerate); caller should bail.

  basic_block pre = outside_e->src;

  // If it's already a simple preheader (one succ = header), reuse it.
  if (!flow_bb_inside_loop_p(loop, pre) &&
      single_succ_p(pre) && single_succ(pre) == header)
    return pre;

  // Otherwise split the incoming edge to create a new preheader.
  return split_edge(outside_e);
}


/* Attempt to recognize loops of the form:
     for (i = 0; i < N; ++i)
       dst[i] = src1[i] + src2[i];
   and replace them with a call to the external kaddv_complete function.  */

unsigned int pass_kaddv_loop::execute(function *fun) {
    fprintf(stderr,"checkpoint 1: pass entry\n");

    if (!loops_for_fn(fun))
        return 0;

    bool changed = false;

    for (auto loop : loops_list(fun, LI_ONLY_INNERMOST)) {
        fprintf(stderr,"checkpoint 2: for loop entry\n");

        if (loop->inner)
            continue;
        fprintf(stderr,"checkpoint 3: loop inner pass\n");

        if (loop->num_nodes != 3 && loop->num_nodes != 2)
            continue;
        fprintf(stderr,"checkpoint 4: loop node count check passed\n");

        basic_block *bbs = get_loop_body(loop);
        basic_block body_bb = NULL;
        basic_block header = loop->header;
        basic_block latch  = loop_latch_edge(loop)->src;

        if (loop->num_nodes == 2) {
            body_bb = header; // body is in header
        } else {
            for (unsigned i = 0; i < loop->num_nodes; i++)
                if (bbs[i] != header && bbs[i] != latch)
                    body_bb = bbs[i];
        }
        free(bbs);

        if (!body_bb)
            continue;
        fprintf(stderr,"checkpoint 5: Found a loop body basic block\n");

        gimple_stmt_iterator gsi = gsi_start_bb(body_bb);
        if (gsi_end_p(gsi))
            continue;
        fprintf(stderr,"checkpoint 6: Loop body has at least one statement\n");

        gimple *stmt = NULL;
        basic_block *body_blocks = get_loop_body(loop);
        for (unsigned b = 0; b < loop->num_nodes; b++) {
            for (gimple_stmt_iterator gsi = gsi_start_bb(body_blocks[b]);
                 !gsi_end_p(gsi); gsi_next(&gsi)) {
        
                gimple *cur = gsi_stmt(gsi);
                if (is_gimple_assign(cur)) {
                    enum tree_code code = gimple_assign_rhs_code(cur);
                    fprintf(stderr,"  debug: stmt in bb %d has rhs_code=%s\n",
                            body_blocks[b]->index, get_tree_code_name(code));
        
                    if (code == PLUS_EXPR) {
                        stmt = cur;
                        fprintf(stderr, "checkpoint 7: Found PLUS_EXPR statement\n");
                        break;
                    }
                }
            }
            if (stmt) break;
        }
        free(body_blocks);
        if (!stmt)
            continue; // no candidate PLUS_EXPR found

        // Safely get operands
        tree lhs  = gimple_assign_lhs(stmt);   // SSA_NAME (e.g., _3)
        tree rhs1 = gimple_assign_rhs1(stmt);  // SSA_NAME (e.g., _1)
        tree rhs2 = gimple_assign_rhs2(stmt);  // SSA_NAME (e.g., _2)
        fprintf(stderr,"checkpoint 8: Retrieved LHS and RHS operands\n");
        
        // Accept SSA_NAME / ARRAY_REF / MEM_REF here
        auto valid_operand = [](tree t){
            return TREE_CODE(t) == SSA_NAME || TREE_CODE(t) == ARRAY_REF || TREE_CODE(t) == MEM_REF;
        };
        if (!valid_operand(lhs) || !valid_operand(rhs1) || !valid_operand(rhs2)) {
            fprintf(stderr,"checkpoint 9: Operand types not as expected\n");
            continue;
        }
        fprintf(stderr,"checkpoint 9: Operand types valid\n");
        
        // Recursively resolve SSA_NAME -> defining RHS until we hit ARRAY_REF or MEM_REF
        std::function<tree(tree)> resolve_ref = [&](tree t)->tree {
            if (TREE_CODE(t) == ARRAY_REF || TREE_CODE(t) == MEM_REF) return t;
            if (TREE_CODE(t) == SSA_NAME) {
                gimple *def = SSA_NAME_DEF_STMT(t);
                if (!def || !is_gimple_assign(def)) return NULL_TREE;
                tree rhs = gimple_assign_rhs1(def);
                return resolve_ref(rhs);
            }
            return NULL_TREE;
        };
        
        // For the PLUS operands (_1, _2), get their loads as ARRAY_REF/MEM_REF
        tree load1 = resolve_ref(rhs1);
        tree load2 = resolve_ref(rhs2);
        if (!load1 || !load2) {
            fprintf(stderr,"checkpoint 9b: Could not resolve refs for PLUS operands\n");
            continue;
        }
        
        // Find the store that uses the PLUS result (lhs is SSA_NAME)
        tree store_ref = NULL_TREE;  // ARRAY_REF or MEM_REF for dst[i]
        {
            bool found_store = false;
            basic_block *bbs2 = get_loop_body(loop);
            for (unsigned b = 0; b < loop->num_nodes && !found_store; ++b) {
                for (gimple_stmt_iterator si = gsi_start_bb(bbs2[b]); !gsi_end_p(si); gsi_next(&si)) {
                    gimple *s = gsi_stmt(si);
                    if (!is_gimple_assign(s)) continue;
                    // looking for: (ARRAY_REF|MEM_REF) = <lhs SSA_NAME>
                    tree l = gimple_assign_lhs(s);
                    if (TREE_CODE(l) != ARRAY_REF && TREE_CODE(l) != MEM_REF) continue;
                    if (TREE_CODE(gimple_assign_rhs1(s)) != SSA_NAME) continue;
                    if (gimple_assign_rhs1(s) == lhs) {
                        store_ref = l;
                        found_store = true;
                        break;
                    }
                }
            }
            free(bbs2);
            if (!store_ref) {
                fprintf(stderr,"checkpoint 9b: PLUS result not stored to memory in this loop\n");
                continue;
            }
        }
        
        // Helpers to get (base, index) from ARRAY_REF or MEM_REF
        auto get_base = [](tree ref)->tree {
            return TREE_CODE(ref) == ARRAY_REF ? TREE_OPERAND(ref, 0)
                 : TREE_CODE(ref) == MEM_REF   ? TREE_OPERAND(ref, 0)
                                               : NULL_TREE;
        };
        auto get_index = [](tree ref)->tree {
            return TREE_CODE(ref) == ARRAY_REF ? TREE_OPERAND(ref, 1)
                 : TREE_CODE(ref) == MEM_REF   ? TREE_OPERAND(ref, 1)  // may be i*stride
                                               : NULL_TREE;
        };
        
        tree idx_dst  = get_index(store_ref);
        tree idx1     = get_index(load1);
        tree idx2     = get_index(load2);
        if (!idx_dst || !idx1 || !idx2) {
            fprintf(stderr,"checkpoint 9b: Missing index expressions\n");
            continue;
        }
        
        // Compare indices (ARRAY_REF indices usually match; MEM_REF may be i*stride)
        if (!operand_equal_p(idx_dst, idx1, 0) || !operand_equal_p(idx_dst, idx2, 0)) {
            fprintf(stderr,"checkpoint 9c: Index mismatch between dst/srcs\n");
            continue;
        }
        fprintf(stderr,"checkpoint 10: Operands have matching index expressions\n");

        // Build loop-invariant pointers for dst/src1/src2.
        // Works for ARRAY_REF (a[i]) and MEM_REF (*p + i*stride).
        auto ptr_from_ref_base0 = [&](tree ref)->tree {
            // Want a `void *` (ptr_type_node) to the start of the buffer.
            if (TREE_CODE(ref) == ARRAY_REF) {
                // ref is like base[i]; create &base[0]
                tree base = TREE_OPERAND(ref, 0);
                tree idx0_type = TREE_TYPE(TREE_OPERAND(ref, 1));
                if (!idx0_type) idx0_type = sizetype;
                tree zero = build_int_cst(idx0_type, 0);
                // ARRAY_REF result type should be element type of base
                tree elem_ty = TREE_TYPE(ref);
                tree ref0 = build4(ARRAY_REF, elem_ty, base, zero, NULL_TREE, NULL_TREE);
                tree addr = build_fold_addr_expr(ref0);                   // &base[0]
                return fold_convert(ptr_type_node, addr);                 // void *
            }
            if (TREE_CODE(ref) == MEM_REF) {
                // ref is MEM_REF (base_ptr, offset). Use base_ptr as start.
                tree basep = TREE_OPERAND(ref, 0);
                return fold_convert(ptr_type_node, basep);                // void *
            }
            return NULL_TREE;
        };
        
        tree dst_ptr  = ptr_from_ref_base0(store_ref);
        tree src1_ptr = ptr_from_ref_base0(load1);
        tree src2_ptr = ptr_from_ref_base0(load2);
        
        if (!dst_ptr || !src1_ptr || !src2_ptr) {
            fprintf(stderr, "checkpoint 9d: failed to form base pointers (dst=%p src1=%p src2=%p)\n",
                    (void*)dst_ptr, (void*)src1_ptr, (void*)src2_ptr);
            continue;
        }
        
        // Element size: use the type of the ref (element type of the array/memory).
        tree elem_ty = TREE_TYPE(store_ref);
        unsigned elem_size = int_size_in_bytes(elem_ty);
        
        // Iteration count (may be unknown; expected_loop_iterations can return 0/UNKNOWN)
        unsigned niter = expected_loop_iterations(loop);
        if (niter == 0 || niter == (unsigned)-1) {
            fprintf(stderr, "checkpoint 9e: unknown iteration count, bailing\n");
            continue;
        }
        tree size = build_int_cst(integer_type_node, niter * elem_size);
        
// --- Ensure preheader and split pre->header edge ---
basic_block pre = get_or_make_preheader(loop);
if (!pre) { fprintf(stderr,"PHERR: no preheader\n"); continue; }
basic_block hdr = loop->header;

edge pe = find_edge(pre, hdr);
if (!pe) { fprintf(stderr,"PHERR: no pre->hdr edge\n"); continue; }

basic_block mid = split_edge(pe);            // needs #include "cfghooks.h"
gimple_stmt_iterator msi = gsi_after_labels(mid);

// --- Build (or reuse) decl: kaddv_complete(u8*, u8*, u8*, int) ---
static tree kaddv_decl = NULL_TREE;
if (!kaddv_decl) {
  tree u8_ptr = build_pointer_type(unsigned_char_type_node);
  tree fntype = build_function_type_list(
      void_type_node, u8_ptr, u8_ptr, u8_ptr, integer_type_node, NULL_TREE);
  kaddv_decl = build_fn_decl("kaddv_complete", fntype);
  TREE_PUBLIC(kaddv_decl) = 1;
  DECL_EXTERNAL(kaddv_decl) = 1;
}

// --- Helper: materialize pointer arg as tmp of type u8* (SSA later) ---
auto materialize_ptr = [&](gimple_stmt_iterator *where, tree expr)->tree {
  tree u8_ptr = build_pointer_type(unsigned_char_type_node);
  tree cast   = fold_convert(u8_ptr, expr);
  tree tmp    = create_tmp_var(u8_ptr, "kvcu_p");   // VAR_DECL; SSA renamer will handle
  gimple *a   = gimple_build_assign(tmp, cast);
  gsi_insert_before(where, a, GSI_NEW_STMT);
  return tmp;
};

// --- Materialize args in the split edge block, then insert the call ---
tree dst_arg  = materialize_ptr(&msi, dst_ptr);
tree src1_arg = materialize_ptr(&msi, src1_ptr);
tree src2_arg = materialize_ptr(&msi, src2_ptr);

gimple *call = gimple_build_call(kaddv_decl, 4, dst_arg, src1_arg, src2_arg, size);
gsi_insert_before(&msi, call, GSI_NEW_STMT);

        //gsi_remove(&gsi, true);
        //unloop(loop, cfg_changed, exit_bbs);

        //BITMAP_FREE(exit_bbs);
        changed = true;
    }

    return changed ? (TODO_cleanup_cfg | TODO_update_ssa) : 0;
}


} // anon namespace

gimple_opt_pass * make_pass_kaddv_loop(gcc::context *ctxt) {
  return new pass_kaddv_loop(ctxt);
}

void riscv_register_kaddv_pass(void) {
  opt_pass *pass = make_pass_kaddv_loop(g);
  struct register_pass_info info = { pass, "cfg",
                                     1, PASS_POS_INSERT_AFTER };
  register_pass(&info);
}