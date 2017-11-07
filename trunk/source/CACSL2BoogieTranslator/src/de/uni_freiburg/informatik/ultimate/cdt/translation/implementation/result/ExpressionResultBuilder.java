package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class ExpressionResultBuilder {

	public final List<Statement> mStatements = new ArrayList<>();
	public LRValue mLrVal;
	public final List<Declaration> mDeclarations = new ArrayList<>();
	public final List<Overapprox> mOverappr = new ArrayList<>();
	public final Map<VariableDeclaration, ILocation> mAuxVars = new LinkedHashMap<>();
	public final List<ExpressionResult> mNeighbourUnionFields = new ArrayList<>();


	public ExpressionResultBuilder(final ExpressionResult assignmentExprRes) {
		mStatements.addAll(assignmentExprRes.stmt);
		mDeclarations.addAll(assignmentExprRes.decl);
		mOverappr.addAll(assignmentExprRes.overappr);
		mAuxVars.putAll(assignmentExprRes.auxVars);
		mNeighbourUnionFields.addAll(assignmentExprRes.otherUnionFields);
		mLrVal = assignmentExprRes.lrVal;
	}

	/**
	 * Creates an ExpressionResultBuidler with empty fields.
	 */
	public ExpressionResultBuilder() {
	}

	public ExpressionResultBuilder setLRVal(final LRValue val) {
		assert mLrVal == null : "LRValue has already been set";
		mLrVal = val;
		return this;
	}

	public ExpressionResultBuilder addStatement(final Statement stm) {
		mStatements.add(stm);
		return this;
	}
	public ExpressionResultBuilder addStatements(final Collection<Statement> stms) {
		mStatements.addAll(stms);
		return this;
	}

	public ExpressionResultBuilder addDeclaration(final Declaration stm) {
		mDeclarations.add(stm);
		return this;
	}
	public ExpressionResultBuilder addDeclarations(final Collection<Declaration> stms) {
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

	public ExpressionResultBuilder putAuxVar(final VariableDeclaration avDecl, final ILocation avLoc) {
		mAuxVars.put(avDecl, avLoc);
		return this;
	}
	public ExpressionResultBuilder putAuxVars(final Map<VariableDeclaration, ILocation> auxVars) {
		mAuxVars.putAll(auxVars);
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

	public ExpressionResult build() {
		return new ExpressionResult(mStatements, mLrVal, mDeclarations, mAuxVars, mOverappr, mNeighbourUnionFields);
	}

	public void addAllExceptLrValue(final ExpressionResult currentFieldInitializer) {
		addDeclarations(currentFieldInitializer.getDeclarations());
		addStatements(currentFieldInitializer.getStatements());
		addOverapprox(currentFieldInitializer.getOverapprs());
		putAuxVars(currentFieldInitializer.getAuxVars());
		addNeighbourUnionFields(currentFieldInitializer.getNeighbourUnionFields());
	}
}