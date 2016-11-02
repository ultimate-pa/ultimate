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
			setResult(mFunc.on(comment));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			setResult(mFunc.on(conditionalBlock));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTDirective directive) {
			setResult(mFunc.on(directive));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTIncludeDirective include) {
			setResult(mFunc.on(include));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			setResult(mFunc.on(literalRegion));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			setResult(mFunc.on(expansion));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTRegularNode node) {
			setResult(mFunc.on(node));
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTTranslationUnit tu) {
			setResult(mFunc.on(tu));
			return PROCESS_ABORT;
		}
	}

	private final IPSTNodeFunction<T> mFunc;

	public PSTNodeFunctionDispatcher(final IPSTNodeFunction<T> func) {
		mFunc = func;
	}

	public T dispatch(final IPSTNode node) {
		final DispatchVisitor action = new DispatchVisitor();
		node.accept(action);
		return action.getResult().orElseGet(() -> mFunc.on(node));
	}
}
