package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

public class InitializerResultBuilder {


	/**
	 * The list holding the children elements.
	 */
	private final List<InitializerResult> mList;

	/**
	 * The initializer contents for this tree node.
	 */
	private final ExpressionResult mExpressionResult;

	/**
	 * It is possible to give a struct initializer that lists the fields out of order by giving designators for each
	 * initialization value.
	 */
	private final String mDesignator;

	public InitializerResultBuilder(final String fieldDesignatorName) {
		mList = new ArrayList<>();
		mExpressionResult = null;
		mDesignator = fieldDesignatorName;
	}

	public InitializerResultBuilder() {
		mList = new ArrayList<>();
		mExpressionResult = null;
		mDesignator = null;
	}

	public InitializerResult build() {
		return new InitializerResult(mExpressionResult, mDesignator, mList);
	}

	public void addListEntry(final InitializerResult r) {
		mList.add(r);
	}
}
