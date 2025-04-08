package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.DynamicLoader;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;

public class VariableTerm {
	public VariableTerm(final boolean mIsInVar, final boolean mIsOutVar, final boolean mIsAuxVar,
			final boolean mIsAssignable, final IProgramVar mProgramVar, final TermVariable mTermVar) {
		isInVar = mIsInVar;
		isOutVar = mIsOutVar;
		isAuxVar = mIsAuxVar;
		isAssignable = mIsAssignable;
		programVar = mProgramVar;
		termvar = mTermVar;
		name = termvar.getName();
	}

	public boolean isConstant() {
		return isInVar;
	}

	public final String name;
	public final boolean isInVar, isOutVar, isAssignable, isAuxVar;
	public final IProgramVar programVar;
	public final TermVariable termvar;

	@Override
	public String toString() {
		return "Variable " + name + (isAuxVar ? "" : (" (of " + programVar.getGloballyUniqueId() + ")")) + " {InVar="
				+ isInVar + ", OutVar=" + isOutVar + ", AuxVar=" + isAuxVar + ", Assignable=" + isAssignable + "}";
	}

	public String toCode() {
		final StringBuilder out = new StringBuilder(isInVar ? "currentState" : "nextState");
		switch (ReturnType.getType(programVar.getSort())) {
		case Array:
			out.append(".getArray(");
			break;
		case BitVector:
			out.append(".getBitVec(");
			break;
		case Boolean:
			out.append(".getBool(");
			break;
		case Int:
			out.append(".getInt(");
			break;
		}

		return out.append(DynamicLoader.getVarLookup(programVar)).append(")").toString();
	}

	private static final HashMap<String, Integer> usedNames = new HashMap<>();

	public TermVariable toSMTTerm(final Theory theory) {
		final String distinctName;
		// when making UnmodifiableTransformulas, one name can only appear once.
		if (isAuxVar) {
			int version = usedNames.getOrDefault(name, 0);
			version++;
			distinctName = name + "_auxvar_v" + version;
			usedNames.put(name, version);
		} else {
			distinctName = name;
		}
		return Util.makeVariable(distinctName, termvar.getSort(), theory);
	}
}
