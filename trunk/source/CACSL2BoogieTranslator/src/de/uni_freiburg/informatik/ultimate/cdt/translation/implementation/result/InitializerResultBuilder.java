package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class InitializerResultBuilder {


	/**
	 * The list holding the children elements.
	 */
	private final List<InitializerResult> mList = new ArrayList<>();

	/**
	 * The initializer contents for this tree node.
	 */
	private ExpressionResult mExpressionResult = null;

	/**
	 * It is possible to give a struct initializer that lists the fields out of order by giving designators for each
	 * initialization value.
	 */
	private String mRootDesignator = null;

//	public InitializerResultBuilder(final String fieldDesignatorName) {
//		mList = new ArrayList<>();
//		mExpressionResult = null;
//		mRootDesignator = fieldDesignatorName;
//	}

	public InitializerResultBuilder() {
	}

//	public InitializerResultBuilder(final ExpressionResult rex) {
//		mList = new ArrayList<>();
//		mExpressionResult = rex;
//		mRootDesignator = null;
//	}

	public InitializerResultBuilder(final InitializerResult initializerResult) {
		// TODO Auto-generated constructor stub
	}

	public InitializerResult build() {
		final ExpressionResult expressionResult = null;
		final List<List<Integer>> treeNodeIds = null;
		final Map<List<Integer>, ExpressionResult> treeNodeIdToRValue = null;
		final Map<List<Integer>, String> treeNodeIdToDesignatorName = null;
		//		return new InitializerResult(mExpressionResult, mDesignator, mList);
		return new InitializerResult(null, expressionResult, treeNodeIds, treeNodeIdToRValue,
				treeNodeIdToDesignatorName);
	}

	public void addListEntry(final InitializerResult r) {
		mList.add(r);
	}

	public InitializerResultBuilder setRootDesignator(final String fieldDesignatorName) {
		if (mRootDesignator != null) {
			throw new IllegalStateException("cannot set root designator twice");
		}
		mRootDesignator = fieldDesignatorName;
		return this;
	}

	public InitializerResultBuilder setRootExpressionResult(final ExpressionResult initializerResult) {
		if (mExpressionResult != null) {
			throw new IllegalStateException("cannot set root designator twice");
		}
		mExpressionResult = initializerResult;
		return this;
	}

	public void copyTreeFrom(final InitializerResult initializerResult) {
		// TODO Auto-generated method stub

	}
}
