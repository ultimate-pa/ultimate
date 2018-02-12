/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

/**
 * Builder of InitializerResults.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class InitializerResultBuilder {

	/**
	 * It is possible to give a struct initializer that lists the fields out of order by giving designators for each
	 * initialization value.
	 */
	private String mRootDesignator = null;

	/**
	 * The initializer contents for this tree node.
	 */
	private ExpressionResult mRootExpressionResult = null;

	/**
	 * The list holding the children elements.
	 */
	private List<InitializerResult> mChildren = null;

	public InitializerResultBuilder() {
		// do nothing
	}

	public InitializerResultBuilder(final InitializerResult initializerResult) {
		mRootDesignator = initializerResult.getRootDesignator();
		mRootExpressionResult = initializerResult.hasRootExpressionResult() ?
				new ExpressionResultBuilder()
				.addAllExceptLrValue(initializerResult.getRootExpressionResult())
				.setLrVal(initializerResult.getRootExpressionResult().getLrValue())
				.build() :
					null;
		mChildren = initializerResult.isInitializerList() ? new ArrayList<>(initializerResult.getList()) : null;
	}

	public InitializerResult build() {
		return new InitializerResult(null, mRootDesignator, mRootExpressionResult, mChildren);
	}

	public void addChild(final InitializerResult r) {
		if (mChildren == null) {
			mChildren = new ArrayList<>();
		}
		mChildren.add(r);
	}

	public InitializerResultBuilder setRootDesignator(final String fieldDesignatorName) {
		if (mRootDesignator != null) {
			throw new IllegalStateException("cannot set root designator twice");
		}
		mRootDesignator = fieldDesignatorName;
		return this;
	}

	public InitializerResultBuilder setRootExpressionResult(final ExpressionResult initializerResult) {
		if (mRootExpressionResult != null) {
			throw new IllegalStateException("cannot set root ExpressionResult twice");
		}
		mRootExpressionResult = initializerResult;
		return this;
	}
}
