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
	private final class DispatchVisitor extends PSTVisitorWithResult<T> {

		@Override
		public int visit(final IPSTComment comment) {
			setResult(func.on(comment));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			setResult(func.on(conditionalBlock));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTDirective directive) {
			setResult(func.on(directive));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTIncludeDirective include) {
			setResult(func.on(include));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			setResult(func.on(literalRegion));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			setResult(func.on(expansion));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTRegularNode node) {
			setResult(func.on(node));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTTranslationUnit tu) {
			setResult(func.on(tu));
			return PROCESS_ABORT;
		}
	}

	private final IPSTNodeFunction<T> func;

	public PSTNodeFunctionDispatcher(final IPSTNodeFunction<T> func) {
		this.func = func;
	}

	public T dispatch(final IPSTNode node) {
		final DispatchVisitor action = new DispatchVisitor();
		node.accept(action);
		return action.getResult().orElseGet(() -> func.on(node));
	}
}