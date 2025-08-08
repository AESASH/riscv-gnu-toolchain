// Gimple Pass to recognize simple vector addition loops and replace them with calls to an external kaddv_complete helper.

#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "target.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "cfgloop.h"
#include "cfgloopmanip.h"
#include "context.h"
#include "riscv-protos.h"
#include "fold-const.h"
#include "gimple-iterator.h"
#include "basic-block.h"

namespace {

const pass_data pass_data_kaddv =
{
  GIMPLE_PASS, /* type */
  "kaddv_loop", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  PROP_loops | PROP_cfg, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0 /* todo_flags_finish */
};

class pass_kaddv_loop : public gimple_opt_pass
{
public:
  pass_kaddv_loop(gcc::context *ctxt) : gimple_opt_pass(pass_data_kaddv, ctxt) {}

  bool gate (function *fun) override { return loops_for_fn (fun); }
  unsigned int execute(function *fun) override;
};

/* Attempt to recognize loops of the form:
     for (i = 0; i < N; ++i)
       dst[i] = src1[i] + src2[i];
   and replace them with a call to the external kaddv_complete function.  */

unsigned int pass_kaddv_loop::execute(function *fun) {
  bool changed = false;

  for (auto loop : loops_list(fun, LI_ONLY_INNERMOST))
    {
      // Scan all statements in the loop to find our candidate statement.
      //gimple *the_stmt = nullptr;
      //int num_stmts = 0;
      //basic_block *bbs = get_loop_body(loop);
      //for (unsigned i = 0; i < loop->num_nodes; i++) {
      //    for (gimple_stmt_iterator gsi = gsi_start_bb(bbs[i]); !gsi_end_p(gsi); gsi_next(&gsi)) {
      //        gimple *stmt = gsi_stmt(gsi);
      //        // We are looking for a simple addition assignment.
      //        if (is_gimple_assign(stmt) && gimple_assign_rhs_code(stmt) == PLUS_EXPR) {
      //            the_stmt = stmt;
      //            num_stmts++;
      //        } else if (gimple_has_side_effects(stmt) && !is_gimple_debug(stmt)) {
      //            // If there are other statements with side effects, this loop is too complex.
      //            num_stmts = -1; // Invalidate
      //            break;
      //        }
      //    }
      //    if (num_stmts == -1) break;
      //}
      //free(bbs);
//
      //// If we didn't find exactly one simple assignment, skip this loop.
      //if (num_stmts != 1)
      //  continue;
//
      //tree lhs = gimple_assign_lhs (the_stmt);
      //tree rhs1 = gimple_assign_rhs1 (the_stmt);
      //tree rhs2 = gimple_assign_rhs2 (the_stmt);
//
      //if (TREE_CODE (lhs) != MEM_REF
      //    || TREE_CODE (rhs1) != MEM_REF
      //    || TREE_CODE (rhs2) != MEM_REF)
      //  continue;
//
      //tree idx = TREE_OPERAND (lhs, 1);
      //if (!operand_equal_p (idx, TREE_OPERAND (rhs1, 1), 0)
      //    || !operand_equal_p (idx, TREE_OPERAND (rhs2, 1), 0))
      //  continue;
//
      //tree dst_ptr = TREE_OPERAND (lhs, 0);
      //tree src1_ptr = TREE_OPERAND (rhs1, 0);
      //tree src2_ptr = TREE_OPERAND (rhs2, 0);
//
      //unsigned elem_size = int_size_in_bytes (TREE_TYPE (lhs));
      //unsigned niter = expected_loop_iterations (loop);
      //tree size = build_int_cst (integer_type_node, niter * elem_size);
//
      static tree kaddv_decl = NULL_TREE;
      //if (!kaddv_decl)
      //  {
          tree fntype = build_function_type_list (void_type_node, ptr_type_node,
                                                 ptr_type_node, ptr_type_node,
                                                 integer_type_node, NULL_TREE);
          kaddv_decl = build_fn_decl ("kaddv_complete", fntype);
          TREE_PUBLIC (kaddv_decl) = 1;
          DECL_EXTERNAL (kaddv_decl) = 1;
      //  }

      //gimple *call = gimple_build_call (kaddv_decl, 4,
      //                                  dst_ptr, src1_ptr, src2_ptr, size);

      basic_block pre = loop_preheader_edge (loop)->src;
      gimple_stmt_iterator psi = gsi_after_labels (pre);
      //gsi_insert_before (&psi, call, GSI_NEW_STMT);

      // Remove the original loop
      unloop(loop, NULL, NULL);
      changed = true;
    }

  return changed ? TODO_cleanup_cfg : 0;
}

} // anon namespace

gimple_opt_pass * make_pass_kaddv_loop(gcc::context *ctxt) {
  return new pass_kaddv_loop(ctxt);
}

void riscv_register_kaddv_pass(void) {
  opt_pass *pass = make_pass_kaddv_loop(g);
  struct register_pass_info info = { pass, "*build_cfg",
                                     1, PASS_POS_INSERT_AFTER };
  register_pass(&info);
}