package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTLiteralRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public final class PSTNodeConsumerDispatcher {
	private final class DispatchVisitor implements IPSTVisitor {

		@Override
		public int defaultVisit(final IPSTNode node) {
			mConsumer.on(node);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTComment comment) {
			mConsumer.on(comment);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTConditionalBlock conditionalBlock) {
			mConsumer.on(conditionalBlock);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTDirective directive) {
			mConsumer.on(directive);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTIncludeDirective include) {
			mConsumer.on(include);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTLiteralRegion literalRegion) {
			mConsumer.on(literalRegion);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTMacroExpansion expansion) {
			mConsumer.on(expansion);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTRegularNode node) {
			mConsumer.on(node);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(final IPSTTranslationUnit tu) {
			mConsumer.on(tu);
			return PROCESS_ABORT;
		}
	}

	private final IPSTNodeConsumer mConsumer;

	public PSTNodeConsumerDispatcher(final IPSTNodeConsumer consumer) {
		mConsumer = consumer;
	}

	public void dispatch(final IPSTNode node) {
		node.accept(new DispatchVisitor());
	}
}
