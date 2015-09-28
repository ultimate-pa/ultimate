/**
 * 
 */
package org.joogie.soot.helper;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;

import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Variable;
import org.joogie.util.Util;

import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.jimple.ParameterRef;
import soot.tagkit.Tag;

/**
 * @author schaef
 *
 */
public class GlobalsCache {

	private final Map<SootMethod, BoogieProcedure> mProcedures;
	private final Map<BoogieProcedure, BoogieProcedureInfo> mProcInfo;
	private final Map<SootField, Variable> mPublicFields;
	private final Map<RefType, Variable> mTypeVariables;

	private final BoogieProgramConstructionDecorator mProgDecl;

	/**
	 * This counter returns consecutive, unique number. might be placed
	 * somewhere else in the future.
	 */
	private Integer mUniqueNumber = 0;

	GlobalsCache(final BoogieProgramConstructionDecorator prog) {
		mProgDecl = prog;
		mTypeVariables = new HashMap<RefType, Variable>();
		mPublicFields = new HashMap<SootField, Variable>();
		mProcInfo = new HashMap<BoogieProcedure, BoogieProcedureInfo>();
		mProcedures = new HashMap<SootMethod, BoogieProcedure>();
	}

	public Integer getUniqueNumber() {
		return mUniqueNumber++;
	}

	public SootMethod findSootMethodForBoogieProcedure(BoogieProcedure proc) {
		BoogieProcedureInfo info = getProcedureInfo(proc);
		if (info == null) {
			return null;
		}
		return info.getSootMethod();
	}

	public BoogieProcedureInfo getProcedureInfo(BoogieProcedure proc) {
		return mProcInfo.get(proc);
	}

	public Variable lookupTypeVariable(RefType t) {
		if (!mTypeVariables.containsKey(t)) {
			Variable v = mProgDecl.getTypeFactory().createTypeVariable(t);
			mTypeVariables.put(t, v);
			mProgDecl.getProgram().addTypeVariable(v);
		}
		return mTypeVariables.get(t);
	}

	public BoogieProcedure lookupProcedure(SootMethod m, HeapMode heapMode) {
		BoogieProcedure proc = null;
		if (!mProcedures.containsKey(m)) {
			proc = createBoogieProcedure(m);
			mProgDecl.getProgram().addProcedure(proc);
			// create the boogie procedure info
			BoogieProcedureInfo procinfo = new BoogieProcedureInfo(mProgDecl, proc, m);
			mProcInfo.put(proc, procinfo);

			// TODO: this is a hack! the exception analysis
			// requires that proc is the "currentProcedure"
			// however, this method is not supposed to change
			// the currentProcedure, so we only change it
			// for a few statements and change it back again.
			BoogieProcedure old_ = mProgDecl.getCurrentProcedure();
			mProgDecl.setCurrentProcedure(proc);

			mProcedures.put(m, proc);
			mProgDecl.addCallDependency(proc);

			mProgDecl.getExceptionAnalysis().addUncaughtExceptionsAndModifiesClause(m, new HashSet<SootMethod>(),
					heapMode);
			// TODO: IS THIS SAFE TO DO? Is it true that all non-static
			// procedures should require that __this is not null?
			if (proc.getThisVariable() != null) {
				proc.addRequires(mProgDecl.getOperatorFunctionFactory().isNotNull(proc.getThisVariable()));
			}
			// undo change to BoogieHelpers.currentProcedure
			mProgDecl.setCurrentProcedure(old_);
		} else {
			proc = mProcedures.get(m);
		}
		return proc;
	}

	private BoogieProcedure createBoogieProcedure(SootMethod method) {
		String procedureName = mProgDecl.getQualifiedName(method);
		Variable returnVariable = mProgDecl.createProcedureReturnVariable(method.getReturnType());

		LocationTag locationTag = createLocationTag(method.getTags());
		String signatureString = method.getSignature();

		LinkedList<Variable> parameterList = new LinkedList<Variable>();
		for (int i = 0; i < method.getParameterCount(); i++) {
			ParameterRef pref = new ParameterRef(method.getParameterType(i), i);
			parameterList.addLast(mProgDecl.createParameterVariable(method, pref));
		}

		Variable thisVariable = mProgDecl.createProcedureThisVariable(method);
		BoogieProcedure proc = new BoogieProcedure(procedureName, returnVariable, locationTag, signatureString,
				parameterList, thisVariable);
		return proc;
	}

	public Variable lookupStaticField(SootField arg0) {
		if (!mPublicFields.containsKey(arg0)) {
			Variable v = mProgDecl.createBoogieVariable(mProgDecl.getQualifiedName(arg0),
					mProgDecl.getTypeFactory().lookupBoogieType(arg0.getType()), false);
			mPublicFields.put(arg0, v);

			mProgDecl.getProgram().addGlobalVar(v);
		}
		return mPublicFields.get(arg0);
	}

	public Variable lookupField(SootField arg0) {
		if (!mPublicFields.containsKey(arg0)) {
			Variable v = mProgDecl.createBoogieVariable(mProgDecl.getQualifiedName(arg0),
					mProgDecl.getTypeFactory().lookupBoogieFieldType(arg0.getType()), false);
			mPublicFields.put(arg0, v);
			mProgDecl.getProgram().addGlobalVar(v);
		}
		return mPublicFields.get(arg0);
	}

	public LocationTag createLocationTag(BoogieProcedure proc) {
		LocationTag locationtag = createLocationTag(getProcedureInfo(proc).getSootMethod().getTags());
		return locationtag;
	}

	public LocationTag createLocationTag(Collection<Tag> tags) {
		StringBuilder commentTag = new StringBuilder();
		int lineNumber = Util.findLineNumber(tags);

		if (lineNumber > 0)
			commentTag.append(" @line: " + lineNumber);

		return new LocationTag(commentTag, lineNumber);
	}

}
