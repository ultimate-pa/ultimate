package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.PSTVisitorWithResult;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;

public final class PSTNodeFunctionDispatcher<T> {
	private final IPSTNodeFunction<T> func;

	public PSTNodeFunctionDispatcher(IPSTNodeFunction<T> func) {
		this.func = func;
	}

	public T dispatch(IPSTNode node) {
		final DispatchVisitor action = new DispatchVisitor();
		node.accept(action);
		return action.getResult().orElseGet(() -> func.on(node));
	}

	private final class DispatchVisitor extends PSTVisitorWithResult<T> {

		@Override
		public int visit(IPSTTranslationUnit tu) {
			setResult(func.on(tu));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTRegularNode node) {
			setResult(func.on(node));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTMacroExpansion expansion) {
			setResult(func.on(expansion));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTIncludeDirective include) {
			setResult(func.on(include));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTDirective directive) {
			setResult(func.on(directive));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTComment comment) {
			setResult(func.on(comment));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTConditionalBlock conditionalBlock) {
			setResult(func.on(conditionalBlock));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTLiteralRegion literalRegion) {
			setResult(func.on(literalRegion));
			return PROCESS_ABORT;
		}
	}
}