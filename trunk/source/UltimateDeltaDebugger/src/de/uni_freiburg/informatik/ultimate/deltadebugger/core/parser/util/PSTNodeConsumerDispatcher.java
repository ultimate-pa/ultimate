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
	private final IPSTNodeConsumer consumer;

	public PSTNodeConsumerDispatcher(IPSTNodeConsumer consumer) {
		this.consumer = consumer;
	}

	public void dispatch(IPSTNode node) {
		node.accept(new DispatchVisitor());
	}

	private final class DispatchVisitor implements IPSTVisitor {

		@Override
		public int defaultVisit(IPSTNode node) {
			consumer.on(node);
			return PROCESS_ABORT;
		}
		
		@Override
		public int visit(IPSTTranslationUnit tu) {
			consumer.on(tu);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTRegularNode node) {
			consumer.on(node);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTMacroExpansion expansion) {
			consumer.on(expansion);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTIncludeDirective include) {
			consumer.on(include);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTDirective directive) {
			consumer.on(directive);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTComment comment) {
			consumer.on(comment);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTConditionalBlock conditionalBlock) {
			consumer.on(conditionalBlock);
			return PROCESS_ABORT;
		}

		@Override
		public int visit(IPSTLiteralRegion literalRegion) {
			consumer.on(literalRegion);
			return PROCESS_ABORT;
		}
	}
}