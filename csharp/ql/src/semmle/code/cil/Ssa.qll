/**
 * Provides the module `Ssa` for working with static single assignment (SSA) form.
 */

private import CIL

/**
 * Provides classes for working with static single assignment (SSA) form.
 */
module Ssa {
  private import internal.SsaImplCommon as SsaImpl

  /** An SSA definition. */
  class Definition extends SsaImpl::Definition {
    /** Gets a read of this SSA definition. */
    final ReadAccess getARead() { SsaImpl::ssaDefReachesRead(_, this, result, _) }

    /** Gets the underlying variable update, if any. */
    final VariableUpdate getVariableUpdate() {
      exists(BasicBlock bb, int i |
        result.updatesAt(bb, i) and
        this.definesAt(result.getVariable(), bb, i)
      )
    }

    /** Gets a first read of this SSA definition. */
    final ReadAccess getAFirstRead() {
      exists(BasicBlock bb1, int i1 |
        this.definesAt(_, bb1, i1) and
        SsaImpl::adjacentVarRead(this, bb1, i1, result)
      )
    }

    /** Gets the location of this SSA definition. */
    Location getLocation() { result = this.getVariableUpdate().getLocation() }
  }

  /** A phi node. */
  class PhiNode extends SsaImpl::PhiNode, Definition {
    final override Location getLocation() { result = this.getBasicBlock().getLocation() }

    final override Definition getAnInput() { result = SsaImpl::PhiNode.super.getAnInput() }
  }
}
