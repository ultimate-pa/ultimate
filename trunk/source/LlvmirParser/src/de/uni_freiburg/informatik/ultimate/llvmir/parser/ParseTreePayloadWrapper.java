package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.util.HashMap;
import java.util.Map;

import org.antlr.v4.runtime.tree.ParseTree;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;

public class ParseTreePayloadWrapper implements IPayload {
	private static final long serialVersionUID = 8074143398717066062L;
	private final Map<String, IAnnotations> mAnnotations = new HashMap<>();
	private final ParseTree mParseTree;

	public ParseTreePayloadWrapper(final ParseTree parseTree) {
		mParseTree = parseTree;
		final IAnnotations annotations = new ParseTreeAnnotationWrapper(parseTree);
		mAnnotations.put(parseTree.getClass().getName(), annotations);
	}

	@Override
	public Map<String, IAnnotations> getAnnotations() {
		if (hasAnnotation()) {
			return mAnnotations;
		}
		return new HashMap<>();

	}

	@Override
	public boolean hasAnnotation() {
		return !mAnnotations.isEmpty();
	}

	public ParseTree getParseTree() {
		return mParseTree;
	}
}
