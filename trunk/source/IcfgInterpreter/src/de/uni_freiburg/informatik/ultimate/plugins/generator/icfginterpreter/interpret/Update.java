package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.NonDeterministicChoice;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ProgramState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.BooleanDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class Update {
	private final Variable mVariable;
	private final IProgramVar mProgramVar;
	private final ExecutionTerm mValueDefinition;
	private final boolean mIsHavoced;
	private final boolean mIsUndefined;
	private final ReturnType mReturnType;
	private final RelationSymbol mRelation;

	static BooleanDomain fullBooleanDomain = null;
	static IntegerDomain fullIntegerDomain = null;

	public static Update getAssignmentUpdate(final Variable variable, final ExecutionTerm equalTerm) {
		return new Update(variable, equalTerm, false, RelationSymbol.EQ);
	}

	// TODO make havocs for OutVars that depend on other OutVars

	public static Update getHavocUpdate(final Variable variable, final ExecutionTerm relativeTerm,
			final RelationSymbol relation) {
		assert relation != RelationSymbol.EQ;
		for (final Variable var : relativeTerm.getVariables()) {
			// Has to not be OutVar or constant (both OutVar and InVar)
			assert !var.getVariableTerm().isOutVar || var.getVariableTerm().isInVar;
		}
		return new Update(variable, relativeTerm, true, relation);
	}

	/**
	 * When a variable is undefined in the next state. Assigns any value of the given type.
	 */
	public static Update getHavocUpdateAny(final IProgramVar programVar, final ReturnType type) {
		final Variable replacementVar;

		final Sort mainSort = programVar.getSort();
		final Theory theory = programVar.getSort().getTheory();
		final TermVariable termVar = Util.makeVariable(programVar.getGloballyUniqueId() + "_Havoc", mainSort, theory);

		switch (type) {
		case Array:
			final Sort[] keyValueSorts = mainSort.getArguments();
			final ReturnType keyType = Util.getType(keyValueSorts[0]);
			final ReturnType valueType = Util.getType(keyValueSorts[1]);
			replacementVar = new VariableArrayTerm(keyType, valueType, false, true, false, true, programVar, termVar);
			break;
		case BitVector:
			return null; // TODO

		case Boolean:
			replacementVar = new VariableBooleanTerm(false, true, false, true, programVar, termVar);
			break;
		case Int:
			replacementVar = new VariableIntegerTerm(false, true, false, true, programVar, termVar);
			break;
		default:
			return null;
		}

		return getHavocUpdateAny(replacementVar);
	}

	/**
	 * When a variable is undefined in the next state. Assigns any value of the given type.
	 */
	public static Update getHavocUpdateAny(final Variable variable) {
		return new Update(variable, variable.getVariableTerm().programVar, null, true, true, RelationSymbol.EQ);
	}

	private Update(final Variable variable, final ExecutionTerm valueDefinition, final boolean isHavoced,
			final RelationSymbol relation) {
		this(variable, variable.getVariableTerm().programVar, valueDefinition, isHavoced, false, relation);
	}

	private Update(final Variable variable, final IProgramVar programVar, final ExecutionTerm valueDefinition,
			final boolean isHavoced, final boolean isUndefined, final RelationSymbol relation) {
		assert !variable.getVariableTerm().isInVar && variable.getVariableTerm().isOutVar;
		assert isUndefined || variable.getTerm().returnType.equals(valueDefinition.returnType);

		mVariable = variable;
		mProgramVar = programVar;
		mValueDefinition = valueDefinition;
		mIsHavoced = isHavoced;
		mReturnType = variable.getTerm().returnType;
		mIsUndefined = isUndefined;
		mRelation = relation;

		if (fullBooleanDomain == null) {
			final Theory theory = variable.getVariableTerm().termvar.getSort().getTheory();
			fullBooleanDomain = Util.constructFullDomain(Util.getSort(ReturnType.Boolean, theory));
			fullIntegerDomain = Util.constructFullDomain(Util.getSort(ReturnType.Int, theory));
		}
	}

	public void apply(final ProgramState state, final NonDeterministicChoice havoc) {
		if (mIsUndefined) {
			putValue(state, havoc.havoc(mVariable, mVariable.getDomain()));
		} else if (mIsHavoced) {
			final Domain<?> fullDomain = mVariable.getDomain();

			// TODO define domain well and calculate it from ExecutionTerm and state
			final Domain<?> valueDomain;
			switch (mRelation) {
			case EQ:
				valueDomain = fullDomain.domainFrom(mValueDefinition.evaluate(state));
				break;
			case DISTINCT:
				valueDomain = fullDomain.complement(fullDomain.domainFrom(mValueDefinition.evaluate(state)));
				break;
			case GEQ:
				valueDomain = fullIntegerDomain
						.greaterEqual(fullIntegerDomain.domainFrom(mValueDefinition.evaluate(state)));
				break;
			case GREATER:
				valueDomain = fullIntegerDomain
						.greaterThen(fullIntegerDomain.domainFrom(mValueDefinition.evaluate(state)));
				break;
			case LEQ:
				valueDomain = fullIntegerDomain
						.lessEqual(fullIntegerDomain.domainFrom(mValueDefinition.evaluate(state)));
				break;
			case LESS:
				valueDomain = fullIntegerDomain
						.lessThen(fullIntegerDomain.domainFrom(mValueDefinition.evaluate(state)));
				break;
			default:
				return;
			}
			putValue(state, havoc.havoc(mVariable, valueDomain));
		} else {
			putValue(state, mValueDefinition.evaluate(state));
		}
	}

	private void putValue(final ProgramState state, final Object value) {
		switch (mReturnType) {
		case Array:
			state.setValue(mProgramVar, (SMTArray) value);
			break;
		case BitVector:
			state.setValue(mProgramVar, (BitVector) value);
			break;
		case Boolean:
			state.setValue(mProgramVar, (Boolean) value);
			break;
		case Int:
			state.setValue(mProgramVar, (Integer) value);
			break;
		}
	}

	@Override
	public String toString() {
		if (mIsUndefined) {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := havoc()";
		} else if (mIsHavoced) {
			return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := havoc(" + mRelation + " "
					+ mValueDefinition + ")";
		}
		return mVariable.getVariableTerm().programVar.getGloballyUniqueId() + " := " + mValueDefinition;
	}
}
