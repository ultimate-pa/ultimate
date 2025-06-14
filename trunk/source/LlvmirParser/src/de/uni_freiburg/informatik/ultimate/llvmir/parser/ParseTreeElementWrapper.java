package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

public class ParseTreeElementWrapper implements IElement {
	private static final long serialVersionUID = 233243407316309392L;
	private final IPayload mPayload;
	private final ParseTree mParseTree;

	public ParseTreeElementWrapper(final ParseTree parseTree) {
		mParseTree = parseTree;
		mPayload = new ParseTreePayloadWrapper(parseTree);
	}

	@Override
	public IPayload getPayload() {
		if (!hasPayload()) {
			return new ParseTreePayloadWrapper(mParseTree);
		}
		return mPayload;
	}

	@Override
	public boolean hasPayload() {
		if (mPayload == null) {
			return false;
		}
		return true;
	}

	public ParseTree getPayloadAsParseTree() {
		return mParseTree;
	}
}
