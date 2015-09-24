/**
 * 
 */
package org.joogie.soot;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.BoogieProgram;
import org.joogie.boogie.LocationTag;
import org.joogie.boogie.expressions.Variable;
import org.joogie.soot.factories.BoogieTypeFactory;
import org.joogie.soot.factories.BoogieVariableFactory;
import org.joogie.soot.factories.RealConstantFactory;
import org.joogie.soot.factories.StringConstantFactory;

import soot.RefType;
import soot.SootField;
import soot.SootMethod;
import soot.jimple.ParameterRef;

/**
 * @author schaef
 *
 */
public class GlobalsCache {

	private HashMap<SootMethod, BoogieProcedure> boogieProcedures = new HashMap<SootMethod, BoogieProcedure>();

	private HashMap<BoogieProcedure, BoogieProcedureInfo> boogieProcInfo = new HashMap<BoogieProcedure, BoogieProcedureInfo>();

	private HashMap<SootField, Variable> publicFields = new HashMap<SootField, Variable>();

	private HashMap<RefType, Variable> typeVariables = new HashMap<RefType, Variable>();

	public SootMethod findSootMethodForBoogieProcedure(BoogieProcedure proc) {
		BoogieProcedureInfo info = getProcedureInfo(proc);
		if (info == null) {
			return null;
		}
		return info.getSootMethod();
	}

	public BoogieProcedureInfo getProcedureInfo(BoogieProcedure proc) {
		return boogieProcInfo.get(proc);
	}

	public Variable lookupTypeVariable(RefType t) {
		if (!typeVariables.containsKey(t)) {
			Variable v = BoogieTypeFactory.createTypeVariable(t);
			typeVariables.put(t, v);
			BoogieProgram.v().addTypeVariable(v);
		}
		return typeVariables.get(t);
	}

	public BoogieProcedure lookupProcedure(SootMethod m, HeapMode heapMode) {
		BoogieProcedure proc = null;
		if (!boogieProcedures.containsKey(m)) {
			proc = createBoogieProcedure(m);
			BoogieProgram.v().addProcedure(proc);
			// create the boogie procedure info
			BoogieProcedureInfo procinfo = new BoogieProcedureInfo(proc, m);
			boogieProcInfo.put(proc, procinfo);

			// TODO: this is a hack! the exception analysis
			// requires that proc is the "currentProcedure"
			// however, this method is not supposed to change
			// the currentProcedure, so we only change it
			// for a few statements and change it back again.
			BoogieProcedure old_ = BoogieHelpers.currentProcedure;
			BoogieHelpers.currentProcedure = proc;

			boogieProcedures.put(m, proc);
			if (!BoogieHelpers.callDependencyMap.containsKey(proc)) {
				BoogieHelpers.callDependencyMap.put(proc, new HashSet<BoogieProcedure>());
				/*
				 * for each procedure we need to consider at least it's own
				 * modified globals
				 */
				BoogieHelpers.callDependencyMap.get(proc).add(proc);
			}
			BoogieExceptionAnalysis.addUncaughtExceptionsAndModifiesClause(m, new HashSet<SootMethod>(), heapMode);
			// TODO: IS THIS SAFE TO DO? Is it true that all non-static
			// procedures should require that __this is not null?
			if (proc.getThisVariable() != null) {
				proc.addRequires(BoogieHelpers.isNotNull(proc.getThisVariable()));
			}
			// undo change to BoogieHelpers.currentProcedure
			BoogieHelpers.currentProcedure = old_;
		} else {
			proc = boogieProcedures.get(m);
		}
		return proc;
	}

	private BoogieProcedure createBoogieProcedure(SootMethod method) {
		String procedureName = BoogieHelpers.getQualifiedName(method);
		Variable returnVariable = BoogieHelpers.createProcedureReturnVariable(method.getReturnType());

		LocationTag locationTag = BoogieHelpers.createLocationTag(method.getTags());
		String signatureString = method.getSignature();

		LinkedList<Variable> parameterList = new LinkedList<Variable>();
		for (int i = 0; i < method.getParameterCount(); i++) {
			ParameterRef pref = new ParameterRef(method.getParameterType(i), i);
			parameterList.addLast(BoogieHelpers.createParameterVariable(method, pref));
		}

		Variable thisVariable = BoogieHelpers.createProcedureThisVariable(method);
		BoogieProcedure proc = new BoogieProcedure(procedureName, returnVariable, locationTag, signatureString,
				parameterList, thisVariable);
		return proc;
	}

	public Variable lookupStaticField(SootField arg0) {
		if (!publicFields.containsKey(arg0)) {
			Variable v = BoogieVariableFactory.v().createBoogieVariable(BoogieHelpers.getQualifiedName(arg0),
					BoogieTypeFactory.lookupBoogieType(arg0.getType()), false);
			publicFields.put(arg0, v);

			BoogieProgram.v().addGlobalVar(v);
		}
		return publicFields.get(arg0);
	}

	public Variable lookupField(SootField arg0) {
		if (!publicFields.containsKey(arg0)) {
			Variable v = BoogieVariableFactory.v().createBoogieVariable(BoogieHelpers.getQualifiedName(arg0),
					BoogieTypeFactory.lookupBoogieFieldType(arg0.getType()), false);
			publicFields.put(arg0, v);
			BoogieProgram.v().addGlobalVar(v);
		}
		return publicFields.get(arg0);
	}

	/**
	 * This counter returns consecutive, unique number. might be placed
	 * somewhere else in the future.
	 */
	private Integer uniqueNumber = 0;

	public Integer getUniqueNumber() {
		return this.uniqueNumber++;
	}

	/*
	 * Singleton stuff
	 */
	public static GlobalsCache v() {
		if (null == instance) {
			instance = new GlobalsCache();
		}
		return instance;
	}

	public static void resetInstance() {
		if (instance != null) {
			instance.boogieProcedures = new HashMap<SootMethod, BoogieProcedure>();
			instance.publicFields = new HashMap<SootField, Variable>();
			instance.typeVariables = new HashMap<RefType, Variable>();
			instance.uniqueNumber = 0;
		}
		BoogieTypeFactory.resetFactory();
		RealConstantFactory.resetFactory();
		StringConstantFactory.resetFactory();
		instance = null;
	}

	private static GlobalsCache instance = null;

	private GlobalsCache() {

	}

}
