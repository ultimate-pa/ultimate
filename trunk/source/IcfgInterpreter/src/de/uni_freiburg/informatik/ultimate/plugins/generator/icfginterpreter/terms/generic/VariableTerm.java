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
			final boolean mIsAssignable, final IProgramVar programVar, final TermVariable termVar) {
		isInVar = mIsInVar;
		isOutVar = mIsOutVar;
		isAuxVar = mIsAuxVar;
		isAssignable = mIsAssignable;
		mProgramVar = programVar;
		mTermVar = termVar;
		mName = termVar.getName();
	}

	public boolean isConstant() {
		return isInVar;
	}

	public final String mName;
	public final boolean isInVar, isOutVar, isAssignable, isAuxVar;
	public final IProgramVar mProgramVar;
	public final TermVariable mTermVar;

	@Override
	public String toString() {
		return "Variable " + mName + (isAuxVar ? "" : (" (of " + mProgramVar.getGloballyUniqueId() + ")")) + " {InVar="
				+ isInVar + ", OutVar=" + isOutVar + ", AuxVar=" + isAuxVar + ", Assignable=" + isAssignable + "}";
	}

	public String toCode() {
		final StringBuilder out = new StringBuilder(isInVar ? "currentState" : "nextState");
		switch (ReturnType.getType(mProgramVar.getSort())) {
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

		return out.append(DynamicLoader.getVarLookup(mProgramVar)).append(")").toString();
	}

	private static final HashMap<String, Integer> usedNames = new HashMap<>();

	public TermVariable toSMTTerm(final Theory theory) {
		return Util.makeVariable(mName, mTermVar.getSort(), theory);
	}

	public TermVariable toDistinctSmtTerm(final Theory theory) {
		// when making UnmodifiableTransformulas, the name of an AuxVar can only appear once.
		final String distinctName;
		if (isAuxVar) {
			int version = usedNames.getOrDefault(mName, 0);
			version++;
			distinctName = mName + "_auxvar_v" + version;
			usedNames.put(mName, version);
		} else {
			distinctName = mName;
		}

		return Util.makeVariable(distinctName, mTermVar.getSort(), theory);
	}

	public VariableTerm replaceTermVariable(final TermVariable termVar) {
		return new VariableTerm(isInVar, isOutVar, isAuxVar, isAssignable, mProgramVar, termVar);
	}
}
