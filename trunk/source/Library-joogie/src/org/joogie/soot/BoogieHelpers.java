/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.soot;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.InvokeExpression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.statements.AssignStatement;
import org.joogie.boogie.types.BoogieType;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.joogie.soot.factories.OperatorFunctionFactory;
import org.joogie.util.Log;
import org.joogie.util.Util;

import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.VoidType;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.tagkit.Tag;

/**
 * @author schaef
 */
public class BoogieHelpers {

	public static HashMap<BoogieProcedure, HashSet<BoogieProcedure>> callDependencyMap = new HashMap<BoogieProcedure, HashSet<BoogieProcedure>>();

	public static BoogieProcedure currentProcedure = null;

	private static String replaceIllegalChars(String s) {
		String ret = s.replace("<", "$la$");
		ret = ret.replace(">", "$ra$");
		ret = ret.replace("[", "$lp$");
		ret = ret.replace("]", "$rp$");
		return ret;
	}

	public static Variable getNullVariable() {
		return BoogieProgram.v().getNullReference();
	}

	public static String getQualifiedName(SootMethod m) {
		StringBuilder sb = new StringBuilder();
		sb.append(m.getReturnType().toString() + "$");
		sb.append(m.getDeclaringClass().getName() + "$");
		sb.append(m.getName() + "$");
		sb.append(m.getNumber());
		return replaceIllegalChars(sb.toString());
	}

	public static String getQualifiedName(Local l) {
		// TODO: check if the name is really unique
		StringBuilder sb = new StringBuilder();
		sb.append(l.getName());

		sb.append(l.getNumber());
		return sb.toString();
	}

	public static String getQualifiedName(StaticFieldRef f) {
		return getQualifiedName(f.getField());
	}

	public static String getQualifiedName(SootField f) {
		StringBuilder sb = new StringBuilder();
		sb.append(f.getType() + "$");
		sb.append(f.getDeclaringClass().getName() + "$");
		sb.append(f.getName());
		sb.append(f.getNumber());
		return replaceIllegalChars(sb.toString());
	}

	public static Variable createProcedureReturnVariable(Type returntype) {
		Variable ret;
		Type t = returntype;
		if (t instanceof VoidType) {
			ret = null;
		} else {
			ret = BoogieVariableFactory.v().createBoogieVariable(
					"__ret", BoogieTypeFactory.lookupBoogieType(returntype),
					false);
		}
		return ret;
	}

	public static Variable createProcedureThisVariable(SootMethod method) {
		// Create this variable
		if (!method.isStatic()) {
			return BoogieVariableFactory.v().createBoogieVariable(
					"__this",
					BoogieTypeFactory.lookupBoogieType(method
							.getDeclaringClass().getType()), false);
		}
		return null;
	}

	public static Variable createParameterVariable(SootMethod m, ParameterRef p) {
		StringBuilder sb = new StringBuilder();
		sb.append("$param_");
		sb.append(p.getIndex());
		return BoogieVariableFactory.v().createBoogieVariable(
				sb.toString(), BoogieTypeFactory.lookupBoogieType(p.getType()),
				false);
	}

	public static Expression isNotNull(Expression e) {
		return OperatorFunctionFactory.v().createBinOp("!=", e,
				BoogieProgram.v().getNullReference());
	}

	public static Expression isNull(Expression e) {
		return OperatorFunctionFactory.v().createBinOp("==", e,
				BoogieProgram.v().getNullReference());
	}

	public static Variable createLocalVar(Local local) {
		return new Variable(BoogieHelpers.getQualifiedName(local),
				BoogieTypeFactory.lookupBoogieType(local.getType()));
	}

	public static LocationTag createLocationTag(List<Tag> tags) {
		StringBuilder commentTag = new StringBuilder();
		int lineNumber = Util.findLineNumber(tags);

		if ( lineNumber > 0)
			commentTag.append(" @line: " + lineNumber);

		return new LocationTag(commentTag, lineNumber);
	}

	public static LocationTag createLocationTag(BoogieProcedure proc) {
		LocationTag locationtag =
				BoogieHelpers.createLocationTag(
				GlobalsCache.v().getProcedureInfo(proc).getSootMethod().getTags()
				);
		return locationtag;
	}

	
	public static InvokeExpression createInvokeExpression(BoogieProcedure proc,
			LinkedList<Expression> args) {
		// The arguments might have to be casted to fit the parameter types.
		// Note that the first argument is the THIS pointer which has to be
		// ignored
		LinkedList<Expression> arguments = new LinkedList<Expression>();
		int offset = 0;
		if (!proc.isStatic()) {
			offset = 1;
			arguments.add(args.getFirst());
		}

		for (int i = 0; i < args.size() - offset; i++) {
			Expression exp = args.get(i + offset);
			BoogieType t = proc.lookupParameter(i).getType();
			arguments.add(OperatorFunctionFactory.v()
					.castIfNecessary(exp, t));
		}
		return new InvokeExpression(proc, arguments);
	}

	public static AssignStatement createAssignment(Expression lhs,
			Expression rhs) {
		Expression rhsExpression = OperatorFunctionFactory.v()
				.castIfNecessary(rhs, lhs.getType());
		if (rhsExpression == null) {
			Log.error(rhs.toBoogie() + " cannot be casted");
			Log.error("from: " + rhs.getType().toBoogie() + " to: "
					+ lhs.getType().toBoogie());
		}
		return new AssignStatement(lhs, rhsExpression);
	}

}
