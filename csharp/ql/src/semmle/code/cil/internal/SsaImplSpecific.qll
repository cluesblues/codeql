/** Provides the CIL specific parameters for `SsaImplCommon.qll`. */

private import cil

class BasicBlock = CIL::BasicBlock;

ControlFlowNode getBasicBlockNode(BasicBlock bb, int i) { result = bb.getNode(i) }

BasicBlock getImmediateDominator(BasicBlock bb) { result = bb.getImmediateDominator() }

class ExitBasicBlock = CIL::ExitBasicBlock;

class ControlFlowNode = CIL::ControlFlowNode;

class SourceVariable = CIL::StackVariable;

private newtype TReadKind = ActualRead()

class ReadKind extends TReadKind {
  string toString() { result = "ActualRead" }
}

predicate variableWrite(BasicBlock bb, int i, SourceVariable v, boolean certain) {
  exists(CIL::VariableUpdate vu |
    vu.updatesAt(bb, i) and
    v = vu.getVariable() and
    certain = true
  )
}

predicate variableRead(BasicBlock bb, int i, SourceVariable v, ReadKind kind) {
  exists(CIL::ReadAccess ra | bb.getNode(i) = ra |
    ra.getTarget() = v and
    kind = ActualRead()
  )
}
