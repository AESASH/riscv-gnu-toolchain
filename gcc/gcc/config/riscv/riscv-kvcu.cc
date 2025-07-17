/* Pass to recognize simple vector addition loops and replace them
   with calls to an external kaddv_complete helper.  */

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
#include "cfgloop.h"
#include "context.h"
#include "target.h"
#include "fold-const.h"
#include "riscv-protos.h"

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

  unsigned int execute(function *fun) override;
};

/* Attempt to recognize loops of the form:
     for (i = 0; i < N; ++i)
       dst[i] = src1[i] + src2[i];
   and replace them with a call to the external kaddv_complete function.  */

unsigned int
pass_kaddv_loop::execute(function *fun)
{
  if (!loops_for_fn(fun))
    return 0;

  bool changed = false;

  for (auto loop : loops_list(fun, LI_ONLY_INNERMOST))
    {
      if (loop->inner)
        continue;

      if (loop->num_nodes != 3 && loop->num_nodes != 2)
        continue;

      basic_block *bbs = get_loop_body (loop);
      basic_block body_bb = NULL;
      basic_block header = loop->header;
      basic_block latch = loop_latch_edge (loop)->src;
      for (unsigned i = 0; i < loop->num_nodes; i++)
        if (bbs[i] != header && bbs[i] != latch)
          body_bb = bbs[i];
      free (bbs);

      if (!body_bb)
        continue;

      gimple_stmt_iterator gsi = gsi_start_bb (body_bb);
      if (gsi_end_p (gsi))
        continue;

      gimple *stmt = gsi_stmt (gsi);
      if (!is_gimple_assign (stmt)
          || gimple_assign_rhs_code (stmt) != PLUS_EXPR)
        continue;

      tree lhs = gimple_assign_lhs (stmt);
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);

      if (TREE_CODE (lhs) != MEM_REF
          || TREE_CODE (rhs1) != MEM_REF
          || TREE_CODE (rhs2) != MEM_REF)
        continue;

      tree idx = TREE_OPERAND (lhs, 1);
      if (!operand_equal_p (idx, TREE_OPERAND (rhs1, 1), 0)
          || !operand_equal_p (idx, TREE_OPERAND (rhs2, 1), 0))
        continue;

      tree dst_ptr = TREE_OPERAND (lhs, 0);
      tree src1_ptr = TREE_OPERAND (rhs1, 0);
      tree src2_ptr = TREE_OPERAND (rhs2, 0);

      unsigned elem_size = int_size_in_bytes (TREE_TYPE (lhs));
      unsigned niter = expected_loop_iterations (loop);
      tree size = build_int_cst (integer_type_node, niter * elem_size);

      static tree kaddv_decl = NULL_TREE;
      if (!kaddv_decl)
        {
          tree fntype = build_function_type_list (void_type_node, ptr_type_node,
                                                 ptr_type_node, ptr_type_node,
                                                 integer_type_node, NULL_TREE);
          kaddv_decl = build_fn_decl ("kaddv_complete", fntype);
          TREE_PUBLIC (kaddv_decl) = 1;
          DECL_EXTERNAL (kaddv_decl) = 1;
        }

      gimple *call = gimple_build_call (kaddv_decl, 4,
                                        dst_ptr, src1_ptr, src2_ptr, size);

      basic_block pre = loop_preheader_edge (loop)->src;
      gimple_stmt_iterator psi = gsi_after_labels (pre);
      gsi_insert_before (&psi, call, GSI_NEW_STMT);

      gsi_remove (&gsi, true);
      changed = true;
    }

  return changed ? TODO_cleanup_cfg : 0;
}

} // anon namespace

gimple_opt_pass *
make_pass_kaddv_loop(gcc::context *ctxt)
{
  return new pass_kaddv_loop(ctxt);
}

void
riscv_register_kaddv_pass(void)
{
  opt_pass *pass = make_pass_kaddv_loop(g);
  struct register_pass_info info = { pass, "*warn_unused_result",
                                     1, PASS_POS_INSERT_AFTER };
  register_pass(&info);
}
