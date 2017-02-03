/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.annotation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark the root node so various tools knows that they
 * should run in LTL mode and which property should be checked.
 * 
 * TODO: Using a check for translation is ugly. This should change.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 */

public class LTLPropertyCheck extends Check {

	private static final long serialVersionUID = 1L;
	private static final String KEY = LTLPropertyCheck.class.getSimpleName();

	@Visualizable
	private final String mLTLProptery;
	private final Map<String, CheckableExpression> mCheckableAtomicPropositions;
	private List<VariableDeclaration> mGlobalDeclarations;

	public LTLPropertyCheck(final String ltlPropertyAsString,
			final Map<String, CheckableExpression> checkableAtomicPropositions,
			final List<VariableDeclaration> globalDeclarations) {
		super(Spec.LTL);
		assert ltlPropertyAsString != null;
		assert checkableAtomicPropositions != null;
		assert !checkableAtomicPropositions.isEmpty();
		mLTLProptery = ltlPropertyAsString;
		mCheckableAtomicPropositions = checkableAtomicPropositions;
		mGlobalDeclarations = globalDeclarations;
	}

	public Map<String, CheckableExpression> getCheckableAtomicPropositions() {
		return mCheckableAtomicPropositions;
	}

	public List<VariableDeclaration> getGlobalDeclarations() {
		if (mGlobalDeclarations == null) {
			mGlobalDeclarations = new ArrayList<>(0);
		}
		return mGlobalDeclarations;
	}

	public String getLTLProperty() {
		return mLTLProptery;
	}

	@Override
	public String getNegativeMessage() {
		return "The LTL property " + mLTLProptery + " was violated.";
	}

	@Override
	public String getPositiveMessage() {
		return "The LTL property " + mLTLProptery + " holds.";
	}

	@Override
	public void annotate(final IElement elem) {
		elem.getPayload().getAnnotations().put(KEY, this);
	}

	public static LTLPropertyCheck getAnnotation(final IElement elem) {
		return ModernAnnotations.getAnnotation(elem, KEY, a -> (LTLPropertyCheck) a);
	}

	/**
	 * 
	 * @author dietsch@informatik.uni-freiburg.de
	 * 
	 */
	public static class CheckableExpression {
		private final Expression mExpression;
		private List<Statement> mStatements;

		public CheckableExpression(final Expression expr, final List<Statement> statements) {
			assert expr != null;
			mExpression = expr;
			mStatements = statements;
		}

		public Expression getExpression() {
			return mExpression;
		}

		public List<Statement> getStatements() {
			if (mStatements == null) {
				mStatements = new ArrayList<>(0);
			}
			return mStatements;
		}

	}

}
