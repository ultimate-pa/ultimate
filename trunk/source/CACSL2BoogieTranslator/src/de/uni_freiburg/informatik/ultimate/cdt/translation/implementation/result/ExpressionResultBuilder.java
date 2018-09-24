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
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;

public class ExpressionResultBuilder {

	private final List<Statement> mStatements = new ArrayList<>();
	private LRValue mLrVal;
	private final List<Declaration> mDeclarations = new ArrayList<>();
	private final List<Overapprox> mOverappr = new ArrayList<>();
	private final Set<AuxVarInfo> mAuxVars = new HashSet<>();
	private final List<ExpressionResult> mNeighbourUnionFields = new ArrayList<>();

	/**
	 * Creates an ExpressionResultBuidler with empty fields.
	 */
	public ExpressionResultBuilder() {
		// do nothing
	}

	/**
	 * copy constructor
	 *
	 * @param builderIn
	 */
	public ExpressionResultBuilder(final ExpressionResultBuilder original) {
		mStatements.addAll(original.getStatements());
		mDeclarations.addAll(original.getDeclarations());
		mOverappr.addAll(original.getOverappr());
		mAuxVars.addAll(original.getAuxVars());
		mNeighbourUnionFields.addAll(original.getNeighbourUnionFields());
		mLrVal = original.getLrValue();
	}

	public ExpressionResultBuilder(final ExpressionResult er) {
		mStatements.addAll(er.getStatements());
		mDeclarations.addAll(er.getDeclarations());
		mOverappr.addAll(er.getOverapprs());
		mAuxVars.addAll(er.getAuxVars());
		mNeighbourUnionFields.addAll(er.getNeighbourUnionFields());
		mLrVal = er.getLrValue();
	}

	public boolean isEmpty() {
		return mStatements.isEmpty() && mDeclarations.isEmpty() && mOverappr.isEmpty() && mAuxVars.isEmpty()
				&& mNeighbourUnionFields.isEmpty() && mLrVal == null;
	}

	public ExpressionResultBuilder setLrValue(final LRValue val) {
		if (mLrVal != null) {
			throw new IllegalStateException("LRValue has already been set");
		}
		mLrVal = val;
		return this;
	}

	public ExpressionResultBuilder addStatement(final Statement stm) {
		mStatements.add(stm);
		return this;
	}

	public <T extends Statement> ExpressionResultBuilder addStatements(final Collection<T> stms) {
		mStatements.addAll(stms);
		return this;
	}

	public ExpressionResultBuilder addDeclaration(final Declaration stm) {
		mDeclarations.add(stm);
		return this;
	}

	public <T extends Declaration> ExpressionResultBuilder addDeclarations(final Collection<T> stms) {
		mDeclarations.addAll(stms);
		return this;
	}

	public ExpressionResultBuilder addOverapprox(final Overapprox oa) {
		mOverappr.add(oa);
		return this;
	}

	public ExpressionResultBuilder addOverapprox(final Collection<Overapprox> oas) {
		mOverappr.addAll(oas);
		return this;
	}

	public ExpressionResultBuilder addAuxVar(final AuxVarInfo auxvar) {
		mAuxVars.add(auxvar);
		return this;
	}

	public ExpressionResultBuilder addAuxVars(final Collection<AuxVarInfo> auxvar) {
		mAuxVars.addAll(auxvar);
		return this;
	}

	public ExpressionResultBuilder addNeighbourUnionField(final ExpressionResult unionField) {
		mNeighbourUnionFields.add(unionField);
		return this;
	}

	public ExpressionResultBuilder addNeighbourUnionFields(final Collection<ExpressionResult> unionFields) {
		mNeighbourUnionFields.addAll(unionFields);
		return this;
	}

	public ExpressionResultBuilder addAllExceptLrValueAndHavocAux(final ExpressionResult exprResult) {
		addAllExceptLrValue(exprResult);
		addStatements(CTranslationUtil.createHavocsForAuxVars(exprResult.getAuxVars()));
		return this;
	}

	public ExpressionResultBuilder addAllExceptLrValue(final ExpressionResult exprResult) {
		addStatements(exprResult.getStatements());
		addAllExceptLrValueAndStatements(exprResult);
		return this;
	}

	/**
	 * Add all statements, declarations, auxVars and overapproximations of the supplied {@link ExpressionResult}s to
	 * this builder.
	 */
	public ExpressionResultBuilder addAllExceptLrValue(final ExpressionResult... resExprs) {
		for (final ExpressionResult resExpr : resExprs) {
			addAllExceptLrValue(resExpr);
		}
		return this;
	}

	/**
	 * Add all statements, declarations, auxVars and overapproximations of the supplied {@link ExpressionResult}s to
	 * this builder.
	 */
	public ExpressionResultBuilder addAllExceptLrValue(final Collection<ExpressionResult> resExprs) {
		for (final ExpressionResult resExpr : resExprs) {
			addAllExceptLrValue(resExpr);
		}
		return this;
	}

	public ExpressionResultBuilder addAllExceptLrValueAndStatements(final ExpressionResult exprResult) {
		addDeclarations(exprResult.getDeclarations());
		addOverapprox(exprResult.getOverapprs());
		addAuxVars(exprResult.getAuxVars());
		if (exprResult.getNeighbourUnionFields() != null && !exprResult.getNeighbourUnionFields().isEmpty()) {
			addNeighbourUnionFields(exprResult.getNeighbourUnionFields());
		}
		return this;
	}

	public ExpressionResult build() {
		return new ExpressionResult(mStatements, mLrVal, mDeclarations, mAuxVars, mOverappr, mNeighbourUnionFields);
	}

	public LRValue getLrValue() {
		return mLrVal;
	}

	public List<Statement> getStatements() {
		return Collections.unmodifiableList(mStatements);
	}

	public List<Declaration> getDeclarations() {
		return Collections.unmodifiableList(mDeclarations);
	}

	public List<Overapprox> getOverappr() {
		return Collections.unmodifiableList(mOverappr);
	}

	public Set<AuxVarInfo> getAuxVars() {
		return Collections.unmodifiableSet(mAuxVars);
	}

	public List<ExpressionResult> getNeighbourUnionFields() {
		return Collections.unmodifiableList(mNeighbourUnionFields);
	}

	public ExpressionResultBuilder resetLrValue(final LRValue rVal) {
		if (mLrVal == null) {
			throw new IllegalStateException("use setLrVal instead");
		}
		mLrVal = rVal;
		return this;
	}

	public ExpressionResultBuilder setOrResetLrValue(final LRValue lrVal) {
		if (mLrVal == null) {
			setLrValue(lrVal);
		} else {
			resetLrValue(lrVal);
		}
		return this;

	}

	/**
	 * Clears the current list of statements and puts the given list in its place.
	 *
	 * @param newStatements
	 */
	public ExpressionResultBuilder resetStatements(final List<Statement> newStatements) {
		mStatements.clear();
		mStatements.addAll(newStatements);
		return this;
	}

	public ExpressionResultBuilder addAllIncludingLrValue(final ExpressionResult expr) {
		return addAllExceptLrValue(expr).setLrValue(expr.getLrValue());
	}

	@Override
	public String toString() {
		return build().toString();
	}

	/**
	 * Remove all aux vars from this builder.
	 */
	public void clearAuxVars() {
		mAuxVars.clear();
	}

}