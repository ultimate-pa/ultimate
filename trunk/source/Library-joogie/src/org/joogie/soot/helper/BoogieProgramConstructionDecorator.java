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

package org.joogie.soot.helper;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.joogie.boogie.BasicBlock;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Expression;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieType;

import soot.Local;
import soot.SootClass;
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
public class BoogieProgramConstructionDecorator {

	private final Map<BoogieProcedure, Set<BoogieProcedure>> mCallDependencyMap;
	private final BoogieProgram mProg;

	private BoogieProcedure mCurrentProcedure;
	private int mFreshVarCounter;

	private OperatorFunctionFactory mFacFunc;
	private BoogieConstantFactory mFacConst;
	private BoogieTypeFactory mFacType;
	private GlobalsCache mCache;
	private BoogieExceptionAnalysis mExceptionAnalysis;

	private BoogieProgramConstructionDecorator(BoogieProgram prog) {
		mProg = prog;
		mCallDependencyMap = new HashMap<BoogieProcedure, Set<BoogieProcedure>>();
		mFreshVarCounter = 0;
		setCurrentProcedure(null);
	}

	public static BoogieProgramConstructionDecorator create(final BoogieProgram prog, final Logger logger) {
		BoogieProgramConstructionDecorator progDec = new BoogieProgramConstructionDecorator(prog);

		progDec.mCache = new GlobalsCache(progDec);
		progDec.mFacFunc = new OperatorFunctionFactory(progDec, logger);
		progDec.mFacConst = new BoogieConstantFactory(progDec);
		progDec.mFacType = new BoogieTypeFactory();
		progDec.mExceptionAnalysis = new BoogieExceptionAnalysis(progDec);

		return progDec;
	}

	public BoogieProgram getProgram() {
		return mProg;
	}

	public void addCallDependency(BoogieProcedure procedure) {
		if (mCallDependencyMap.containsKey(procedure)) {
			return;
		}

		final Set<BoogieProcedure> set = new HashSet<BoogieProcedure>();
		set.add(procedure);
		mCallDependencyMap.put(procedure, set);
	}

	private String replaceIllegalChars(String s) {
		String ret = s.replace("<", "$la$");
		ret = ret.replace(">", "$ra$");
		ret = ret.replace("[", "$lp$");
		ret = ret.replace("]", "$rp$");
		return ret;
	}

	public Variable getNullVariable() {
		return mProg.getNullReference();
	}

	public BoogieProcedure getCurrentProcedure() {
		return mCurrentProcedure;
	}

	public void setCurrentProcedure(BoogieProcedure proc) {
		mCurrentProcedure = proc;
	}

	public String getQualifiedName(SootMethod m) {
		StringBuilder sb = new StringBuilder();
		sb.append(m.getReturnType().toString() + "$");
		sb.append(m.getDeclaringClass().getName() + "$");
		sb.append(m.getName() + "$");
		sb.append(m.getNumber());
		return replaceIllegalChars(sb.toString());
	}

	public String getQualifiedName(Local l) {
		// TODO: check if the name is really unique
		StringBuilder sb = new StringBuilder();
		sb.append(l.getName());

		sb.append(l.getNumber());
		return sb.toString();
	}

	public String getQualifiedName(StaticFieldRef f) {
		return getQualifiedName(f.getField());
	}

	public String getQualifiedName(SootField f) {
		StringBuilder sb = new StringBuilder();
		sb.append(f.getType() + "$");
		sb.append(f.getDeclaringClass().getName() + "$");
		sb.append(f.getName());
		sb.append(f.getNumber());
		return replaceIllegalChars(sb.toString());
	}

	public Variable createProcedureReturnVariable(Type returntype) {
		Variable ret;
		Type t = returntype;
		if (t instanceof VoidType) {
			ret = null;
		} else {
			ret = createBoogieVariable("__ret", mFacType.lookupBoogieType(returntype));
		}
		return ret;
	}

	public Variable createProcedureThisVariable(SootMethod method) {
		// Create this variable
		if (!method.isStatic()) {
			return createBoogieVariable("__this", mFacType.lookupBoogieType(method.getDeclaringClass().getType()));
		}
		return null;
	}

	public Variable createParameterVariable(SootMethod m, ParameterRef p) {
		StringBuilder sb = new StringBuilder();
		sb.append("$param_");
		sb.append(p.getIndex());
		return createBoogieVariable(sb.toString(), mFacType.lookupBoogieType(p.getType()));
	}

	public Variable createLocalVar(Local local) {
		return new Variable(getQualifiedName(local), mFacType.lookupBoogieType(local.getType()));
	}

	public Expression getFreshLocalVariable(BoogieType t) {
		return getFreshLocalVariable("$freshlocal", t);
	}

	public Variable getFreshLocalVariable(String prefix, BoogieType t) {
		return getCurrentProcedure().getFreshLocalVariable(prefix, t);
	}

	public Expression getFreshGlobalConstant(BoogieType t) {
		Variable v = new Variable("$fresh" + String.valueOf((++mFreshVarCounter)), t);
		mProg.addGlobalVar(v);
		return v;
	}

	public Variable createBoogieVariable(String name, BoogieType t) {
		return new Variable(name, t);
	}

	public OperatorFunctionFactory getOperatorFunctionFactory() {
		return mFacFunc;
	}

	public BoogieTypeFactory getTypeFactory() {
		return mFacType;
	}

	public BoogieConstantFactory getConstantFactory() {
		return mFacConst;
	}

	public GlobalsCache getCache() {
		return mCache;
	}

	public BoogieExceptionAnalysis getExceptionAnalysis() {
		return mExceptionAnalysis;
	}

	public String getUniqueUid() {
		return mCache.getUniqueNumber().toString();
	}

	public BasicBlock createBasicBlock(Collection<Tag> tags) {
		return new BasicBlock(mCache.createLocationTag(tags), getUniqueUid());
	}

	public BasicBlock createBasicBlock(BoogieProcedure procedure) {
		return new BasicBlock(mCache.createLocationTag(procedure), getUniqueUid());
	}

	public BasicBlock createBasicBlock(LocationTag locationTag) {
		return new BasicBlock(locationTag, getUniqueUid());
	}

	public Map<BoogieProcedure, Set<BoogieProcedure>> getCallDependencyMap() {
		return mCallDependencyMap;
	}

}
