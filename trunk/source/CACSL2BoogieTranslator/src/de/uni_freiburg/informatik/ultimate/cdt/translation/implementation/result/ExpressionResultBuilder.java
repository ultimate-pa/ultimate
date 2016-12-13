package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class ExpressionResultBuilder {

	public final List<Statement> mStatements = new ArrayList<>();
	public LRValue mLrVal;
	public final List<Declaration> mDeclarations = new ArrayList<>(); 
	public final List<Overapprox> mOverappr = new ArrayList<>();
	public final Map<VariableDeclaration, ILocation> mAuxVars = new LinkedHashMap<>();
	public final List<ExpressionResult> mNeighbourUnionFields = new ArrayList<>();
	
	
	public ExpressionResultBuilder(ExpressionResult assignmentExprRes) {
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

	public ExpressionResultBuilder setLRVal(LRValue val) {
		assert mLrVal == null : "LRValue has already been set";
		mLrVal = val;
		return this;
	}

	public ExpressionResultBuilder addStatement(Statement stm) {
		mStatements.add(stm);
		return this;
	}
	public ExpressionResultBuilder addStatements(Collection<Statement> stms) {
		mStatements.addAll(stms);
		return this;
	}
	
	public ExpressionResultBuilder addDeclaration(Declaration stm) {
		mDeclarations.add(stm);
		return this;
	}
	public ExpressionResultBuilder addDeclarations(Collection<Declaration> stms) {
		mDeclarations.addAll(stms);
		return this;
	}
	
	public ExpressionResultBuilder addOverapprox(Overapprox oa) {
		mOverappr.add(oa);
		return this;
	}
	public ExpressionResultBuilder addOverapprox(Collection<Overapprox> oas) {
		mOverappr.addAll(oas);
		return this;
	}
	
	public ExpressionResultBuilder putAuxVar(VariableDeclaration avDecl, ILocation avLoc) {
		mAuxVars.put(avDecl, avLoc);
		return this;
	}
	public ExpressionResultBuilder putAuxVars(Map<VariableDeclaration, ILocation> auxVars) {
		mAuxVars.putAll(auxVars);
		return this;
	}

	public ExpressionResultBuilder addNeighbourUnionField(ExpressionResult unionField) {
		mNeighbourUnionFields.add(unionField);
		return this;
	}
	public ExpressionResultBuilder addNeighbourUnionFields(Collection<ExpressionResult> unionFields) {
		mNeighbourUnionFields.addAll(unionFields);
		return this;
	}
	
	public ExpressionResult build() {
		return new ExpressionResult(mStatements, mLrVal, mDeclarations, mAuxVars, mOverappr, mNeighbourUnionFields);
	}
}