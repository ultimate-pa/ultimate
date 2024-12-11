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
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;

/**
 * When the RCFG is used as a Büchi program, use this Annotation to mark the root node so various tools knows that they
 * should run in LTL mode and which property should be checked.
 *
 * TODO: Using a check for translation is ugly. This should change.
 * 
 * TODO: Overwrite equals and hashcode if you want to keep using this class
 *
 * @author dietsch@informatik.uni-freiburg.de
 */

public class LTLPropertyCheck extends Check {

	private static final long serialVersionUID = 1L;
	private static final String KEY = LTLPropertyCheck.class.getSimpleName();

	@Visualizable
	private final String mUltimateLTLProptery;
	private final Map<String, CheckableExpression> mCheckableAtomicPropositions;
	private final List<VariableDeclaration> mGlobalDeclarations;
	private final String mLTL2BALTLProptery;

	public LTLPropertyCheck(final String ltlPropertyAsString,
			final Map<String, CheckableExpression> checkableAtomicPropositions,
			final List<VariableDeclaration> globalDeclarations) {
		super(Spec.LTL);
		assert ltlPropertyAsString != null : "There is no property";
		assert checkableAtomicPropositions != null : "There is a property the map between APs and Boogie expressions is not there";
		assert !checkableAtomicPropositions
				.isEmpty() : "The map between APs and Boogie expressions is empty (remember, even true and false are Boogie expressions)";
		mUltimateLTLProptery = prettyPrintProperty(checkableAtomicPropositions, ltlPropertyAsString);
		mLTL2BALTLProptery = getLTL2BAProperty(ltlPropertyAsString);
		mCheckableAtomicPropositions = checkableAtomicPropositions;
		if (globalDeclarations == null) {
			mGlobalDeclarations = Collections.emptyList();
		} else {
			mGlobalDeclarations = globalDeclarations;
		}
	}

	public Map<String, CheckableExpression> getCheckableAtomicPropositions() {
		return mCheckableAtomicPropositions;
	}

	public List<VariableDeclaration> getGlobalDeclarations() {
		return mGlobalDeclarations;
	}

	public String getUltimateLTLProperty() {
		return mUltimateLTLProptery;
	}

	public String getLTL2BALTLProperty() {
		return mLTL2BALTLProptery;
	}

	@Override
	public String getNegativeMessage() {
		return "The LTL property " + mUltimateLTLProptery + " was violated.";
	}

	@Override
	public String getPositiveMessage() {
		return "The LTL property " + mUltimateLTLProptery + " holds.";
	}

	private static String prettyPrintProperty(final Map<String, CheckableExpression> irs, final String property) {
		String rtr = property;
		for (final Entry<String, CheckableExpression> entry : irs.entrySet()) {
			rtr = rtr.replaceAll(entry.getKey(),
					"(" + BoogiePrettyPrinter.print(entry.getValue().getExpression()) + ")");
		}
		return rtr;
	}

	private static String getLTL2BAProperty(final String ltlProperty) {
		String rtr = ltlProperty.toLowerCase();
		rtr = rtr.replaceAll("\\bf\\b", " <> ");
		rtr = rtr.replaceAll("\\bg\\b", " [] ");
		rtr = rtr.replaceAll("\\bx\\b", " X ");
		rtr = rtr.replaceAll("\\bu\\b", " U ");
		rtr = rtr.replaceAll("\\br\\b", " V ");
		rtr = rtr.replaceAll("<==>", "<->");
		rtr = rtr.replaceAll("==>", "->");
		rtr = rtr.replaceAll("\\s+", " ");
		return rtr;
	}

	@Override
	public void annotate(final IElement elem) {
		elem.getPayload().getAnnotations().put(KEY, this);
	}

	public static LTLPropertyCheck getAnnotation(final IElement elem) {
		return ModelUtils.getAnnotation(elem, KEY, a -> (LTLPropertyCheck) a);
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
