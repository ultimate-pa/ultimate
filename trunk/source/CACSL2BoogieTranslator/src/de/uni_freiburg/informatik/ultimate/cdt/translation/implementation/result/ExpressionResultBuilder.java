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

	public final List<Statement> stmt = new ArrayList<>();
	public LRValue lrVal;
	public final List<Declaration> decl = new ArrayList<>(); 
	public final List<Overapprox> overappr = new ArrayList<>();
	public final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
	public final List<ExpressionResult> otherUnionFields = new ArrayList<>();
	
	
	public ExpressionResultBuilder(ExpressionResult assignmentExprRes) {
		stmt.addAll(assignmentExprRes.stmt);
		decl.addAll(assignmentExprRes.decl);
		overappr.addAll(assignmentExprRes.overappr);
		auxVars.putAll(assignmentExprRes.auxVars);
		otherUnionFields.addAll(assignmentExprRes.otherUnionFields);
		lrVal = assignmentExprRes.lrVal;
	}

	/**
	 * Creates an ExpressionResultBuidler with empty fields.
	 */
	public ExpressionResultBuilder() {
	}

	public ExpressionResultBuilder setLRVal(LRValue val) {
		assert lrVal == null : "LRValue has already been set";
		lrVal = val;
		return this;
	}

	public ExpressionResultBuilder addStatement(Statement stm) {
		stmt.add(stm);
		return this;
	}
	public ExpressionResultBuilder addStatements(Collection<Statement> stms) {
		stmt.addAll(stms);
		return this;
	}
	
	public ExpressionResultBuilder addDeclaration(Declaration stm) {
		decl.add(stm);
		return this;
	}
	public ExpressionResultBuilder addDeclarations(Collection<Declaration> stms) {
		decl.addAll(stms);
		return this;
	}
	
	public ExpressionResultBuilder addOverapprox(Overapprox oa) {
		overappr.add(oa);
		return this;
	}
	public ExpressionResultBuilder addOverapprox(Collection<Overapprox> oas) {
		overappr.addAll(oas);
		return this;
	}
	
	public ExpressionResultBuilder putAuxVar(VariableDeclaration avDecl, ILocation avLoc) {
		auxVars.put(avDecl, avLoc);
		return this;
	}
	public ExpressionResultBuilder putAuxVars(Map<VariableDeclaration, ILocation> auxVars) {
		auxVars.putAll(auxVars);
		return this;
	}

	public ExpressionResultBuilder addNeighbourUnionField(ExpressionResult unionField) {
		otherUnionFields.add(unionField);
		return this;
	}
	public ExpressionResultBuilder addNeighbourUnionFields(Collection<ExpressionResult> unionFields) {
		otherUnionFields.addAll(unionFields);
		return this;
	}
	
	public ExpressionResult build() {
		return new ExpressionResult(stmt, lrVal, decl, auxVars, overappr, otherUnionFields);
	}
}