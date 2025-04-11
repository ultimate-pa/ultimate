package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.BooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.AndTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.DistinctTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.EqualsTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.GreaterTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessEqualTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.LessTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.OrTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.VariableTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.AdditionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.NegationTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.SubtractionTerm;

public class ArcSolver {
	private final VariableSet mVariables;
	private final HashSet<Variable> mDefinedVariables;
	private final HashMap<Variable, ArrayList<Constraint>> mConstraints = new HashMap<>();
	private final HashMap<Variable, ArrayList<Arc>> mArcs = new HashMap<>();
	private final int constraintCount;

	/**
	 * @param constraintList should be an {@link AndTerm} from {@link OrTerm#getSubTerms()} of an OrTerm created by
	 *                       {@link TermNormalizer#simplifyToDNF(BooleanTerm)}
	 */
	public ArcSolver(final AndTerm constraintTerm, final ManagedScript managedScript, final VariableSet variables,
			final Theory theory) {
		mVariables = variables;
		mDefinedVariables = new HashSet<>();

		for (final BooleanTerm constraint : constraintTerm.getSubTerms()) {
			final HashSet<Variable> containedOutVars = Util.filter(constraint.getVariables(), (var) -> {
				final VariableTerm varTerm = var.getVariableTerm();
				return (varTerm.isOutVar || varTerm.isAuxVar) && !varTerm.isInVar;
			});

			if (containedOutVars.isEmpty()) {
				continue;
				// does not constrain next state variables, may only be a guard
			}

			BinaryRelation binRel;
			final Term constraintSMT = constraint.toSMTTerm(theory);
			if (constraint.getSubTerms().get(0).returnType == ReturnType.Int) {
				binRel = BinaryNumericRelation.convert(constraintSMT);
			} else {
				binRel = BinaryEqualityRelation.convert(constraintSMT);
			}

			for (final Variable var : mVariables.getVariables()) {
				final BooleanTerm mySolution = solveForSubject(constraint, var);
				if (var.getVariableTerm().isInVar) {
					// We do not need to solve equations for InVars, they are a known constant in a transition.
					continue;
				}
				final Term termVar = var.getTerm().toSMTTerm(theory);

				final SolvedBinaryRelation solvedBinEQ = binRel.solveForSubject(managedScript.getScript(), termVar);
				if (solvedBinEQ != null && mySolution == null) {
					System.out.println("bad");
				}

				if (mySolution == null) {
					continue;
				}

				final ExecutionTerm rightHandSide = mySolution.getSubTerms().get(1);
				RelationSymbol relation;
				switch (mySolution) {
				case final GreaterTerm gt:
					relation = RelationSymbol.GREATER;
					break;
				case final GreaterEqualTerm gt:
					relation = RelationSymbol.GEQ;
					break;
				case final LessTerm gt:
					relation = RelationSymbol.LESS;
					break;
				case final LessEqualTerm gt:
					relation = RelationSymbol.LEQ;
					break;
				case final DistinctTerm gt:
					relation = RelationSymbol.DISTINCT;
					break;
				case final EqualsTerm gt:
					relation = RelationSymbol.EQ;
					break;
				default:
					continue;
				}

				if (rightHandSide.getVariables().size() == 0) {
					final ArrayList<Constraint> varConstraints = mConstraints.getOrDefault(var, new ArrayList<>());
					varConstraints.add(new Constraint(var, rightHandSide, relation));
					mConstraints.put(var, varConstraints);
				} else {
					final ArrayList<Arc> varArcs = mArcs.getOrDefault(var, new ArrayList<>());
					varArcs.add(new Arc(var, rightHandSide, relation));
					mArcs.put(var, varArcs);
				}
				mDefinedVariables.add(var);
			}

		}

		for (final ArrayList<Constraint> constraints : mConstraints.values()) {
			constraints.sort((a, b) -> {
				return a.getVariable().getName().compareTo(b.getVariable().getName());
			});
		}
		for (final ArrayList<Arc> arcs : mArcs.values()) {
			arcs.sort((a, b) -> {
				return a.getDefinedVariable().getName().compareTo(b.getDefinedVariable().getName());
			});
		}

		constraintCount = mConstraints.size() + mArcs.size();

		mUpdates = makeUpdates(managedScript);
	}

	public boolean hasConstraints() {
		return constraintCount > 0;
	}

	public UnmodifiableTransFormula makeGuardFormula(final ManagedScript script, final IUltimateServiceProvider service,
			final ExecutionTerm term, final Infeasibility infeasibility,
			final Collection<TermVariable> branchEncoders) {

		final HashMap<IProgramVar, TermVariable> inVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getInVars().entrySet()) {
			inVars.put(entry.getValue().getVariableTerm().mProgramVar, entry.getKey());
		}
		final HashMap<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (final Entry<TermVariable, Variable> entry : mVariables.getOutVars().entrySet()) {
			outVars.put(entry.getValue().getVariableTerm().mProgramVar, entry.getKey());
		}

		final TransFormulaBuilder formulaBuilder = new TransFormulaBuilder(inVars, outVars, false, null,
				branchEncoders.isEmpty(), branchEncoders, false);

		final Theory theory = script.getScript().getTheory();

		/*
		 * for (final Entry<TermVariable, Variable> entry : mVariables.getAuxVars().entrySet()) { final TermVariable
		 * auxVar = entry.getValue().getVariableTerm().toDistinctSmtTerm(theory);
		 *
		 * final Variable newVar = entry.getValue().replaceTermVariable(auxVar); term =
		 * term.replaceTerm(entry.getValue().getTerm(), newVar.getTerm()); formulaBuilder.addAuxVar(auxVar); }
		 */

		final Term smtTerm = term.toSMTTerm(theory);

		formulaBuilder.setFormula(smtTerm);
		formulaBuilder.setInfeasibility(infeasibility);
		final UnmodifiableTransFormula subTermFormula = formulaBuilder.finishConstruction(script);
		return TransFormulaUtils.computeGuard(subTermFormula, script, service);
	}

	private final Update[] mUpdates;

	public Update[] getUpdates() {
		return mUpdates;
	}

	private Update[] makeUpdates(final ManagedScript script) {
		final ArrayList<Update> updates = new ArrayList<>();

		final Collection<Variable> inVars = mVariables.getInVars().values();
		final HashSet<Variable> wellDefined = new HashSet<>(inVars);

		// get all updates that are in the form wellDefinedVar = Term(const, const, ...)
		for (final Entry<Variable, ArrayList<Constraint>> entry : mConstraints.entrySet()) {
			for (final Constraint constraint : entry.getValue()) {
				if (constraint.relation == RelationSymbol.EQ) {
					updates.add(Update.getAssignmentUpdate(entry.getKey(), constraint.getConstraint()));
					wellDefined.add(entry.getKey());
				}
			}
		}

		eliminateAuxVar(wellDefined);
		final HashSet<Variable> dependentVars = new HashSet<>();
		propagateWellDefined(wellDefined, dependentVars, updates);

		// All remaining variables have to be havoced, or depend on a variable that has to be havoced.

		final HashMap<IProgramVar, Variable> inProgVars = Util.map(inVars, (var) -> {
			return Map.entry(var.getVariableTerm().mProgramVar, var);
		}, new HashMap<>());

		final HashMap<IProgramVar, Variable> assignableProgVars = Util.map(mVariables.getOutVars().values(), (var) -> {
			return Map.entry(var.getVariableTerm().mProgramVar, var);
		}, new HashMap<>());

		// Make updates for variables that are not defined in the next state (havoc any value), this happens when:
		// A. The OutVars do not contain a variable that is in the InVars.
		// B. A variable of the OutVars does not appear in the InVars or the term. (Same for AuxVars)
		for (final Entry<IProgramVar, Variable> inVar : inProgVars.entrySet()) {
			if (assignableProgVars.containsKey(inVar.getKey())) {
				// The program variable has a defining term variable in the next state
				continue;
			}
			updates.add(Update.getHavocUpdateAny(inVar.getKey(), inVar.getValue().getTerm().returnType));
			wellDefined.add(inVar.getValue());
		}
		for (final Entry<IProgramVar, Variable> outVar : assignableProgVars.entrySet()) {
			if (mDefinedVariables.contains(outVar.getValue()) || inProgVars.containsKey(outVar.getKey())) {
				// The TermVariable has some constraint in the term or is constant (inVar and outVar)
				continue;
			}
			updates.add(Update.getHavocUpdateAny(outVar.getValue()));
			wellDefined.add(outVar.getValue());
		}
		/*
		 * for (final Variable auxVar : mVariables.getAuxVars().values()) { if (mDefinedVariables.contains(auxVar)) { //
		 * The TermVariable has some constraint in the term continue; }
		 *
		 * final AuxProgramVar tempVar = AuxProgramVar.makeAuxProgramVariable(auxVar.getVariableTerm().mTermVar,
		 * script); updates.add(Update.getHavocUpdateAny(auxVar.replaceIProgramVar(tempVar)));
		 *
		 * replaceAuxWithValue(auxVar, IcfgTranslation.getVariables(null, script) tempVar.getTermVariable());
		 *
		 * wellDefined.add(auxVar); }
		 */

		eliminateAuxVar(wellDefined);
		propagateWellDefined(wellDefined, dependentVars, updates);

		/*
		 * If a variable is not well defined but not dependent on variables that aren't well defined, it can be havoced
		 * at will. Such a variable would also not have any other variables that depend on it, as any arc var_a < var_b
		 * would lead to an arc var_b > var_a when initially solving BinaryRelations.
		 */

		final HashSet<Variable> independentVars = Util.filter(mVariables.getVariables(), (variable) -> {
			return !(wellDefined.contains(variable) || dependentVars.contains(variable)
					|| mVariables.getAuxVars().containsValue(variable));
		});

		for (final Variable independentVar : independentVars) {
			updates.add(
					Update.getHavocUpdate(independentVar, mConstraints.getOrDefault(independentVar, new ArrayList<>()),
							mArcs.getOrDefault(independentVar, new ArrayList<>())));
			wellDefined.add(independentVar);
		}

		eliminateAuxVar(wellDefined);
		propagateWellDefined(wellDefined, dependentVars, updates);

		// TODO Take care of outVars that depend on other outVars

		return Util.fillArray(updates, new Update[updates.size()]);
	}

	private void replaceAuxWithValue(final Variable varToReplace, final ExecutionTerm replacement) {
		for (final Variable variable : mDefinedVariables) {
			final ArrayList<Arc> arcs = mArcs.getOrDefault(variable, new ArrayList<>());
			for (int i = 0; i < arcs.size(); i++) {
				final Arc arc = arcs.get(i);
				final ExecutionTerm newConstraint = arc.getConstraint().replaceTerm(varToReplace.getTerm(),
						replacement);
				arcs.set(i, new Arc(variable, newConstraint, arc.relation));
			}
			final ArrayList<Constraint> constraints = mConstraints.getOrDefault(variable, new ArrayList<>());
			for (int i = 0; i < constraints.size(); i++) {
				final Constraint constraint = constraints.get(i);
				final ExecutionTerm newConstraint = constraint.getConstraint().replaceTerm(varToReplace.getTerm(),
						replacement);
				constraints.set(i, new Constraint(variable, newConstraint, constraint.relation));
			}
		}
	}

	public void eliminateAuxVar(final HashSet<Variable> wellDefined) {
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Variable variable : mVariables.getAuxVars().values()) {
				// Replace defined AuxVars (auxVar == term) in their term, so
				// [var_a = (var_aux = 3), var_aux = 4] becomes [var_a = (4 = 3)]
				for (final Constraint constraint : mConstraints.getOrDefault(variable, new ArrayList<>())) {
					if (constraint.relation.equals(RelationSymbol.EQ)
							&& wellDefined.containsAll(constraint.getConstraint().getVariables())) {
						// replace the AuxVar with its definition in every other arc and constraint
						replaceAuxWithValue(variable, constraint.getConstraint());
						wellDefined.add(variable);
						unchanged = false;
						break;
					}
				}
			}
		}
	}

	// get all updates that are well defined in the form wellDefinedVar = Term(const, ..., wellDefinedVar, ...)
	private void propagateWellDefined(final HashSet<Variable> wellDefined, final HashSet<Variable> dependentVars,
			final ArrayList<Update> updates) {
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (final Variable variable : mDefinedVariables) {
				if (wellDefined.contains(variable) || variable.getVariableTerm().isAuxVar) {
					continue;
				}
				for (final Arc arc : mArcs.getOrDefault(variable, new ArrayList<>())) {
					if (wellDefined.contains(arc.getDefinedVariable())) {
						continue;
					}
					if (arc.relation != RelationSymbol.EQ) {
						continue;
					}
					if (!wellDefined.containsAll(arc.getVariables())) {
						dependentVars.add(arc.getDefinedVariable());
						continue;
					}
					// this variable is equal to a term that only contains well defined variables
					updates.add(Update.getAssignmentUpdate(arc.getDefinedVariable(), arc.getConstraint()));
					unchanged = false;
					wellDefined.add(arc.getDefinedVariable());
					dependentVars.remove(arc.getDefinedVariable());
				}
			}

		}
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof ArcSolver)) {
			return false;
		}
		final ArcSolver bCast = (ArcSolver) b;

		return mConstraints.equals(bCast.mConstraints) && mArcs.equals(bCast.mArcs)
				&& mVariables.equals(bCast.mVariables);
	}

	@Override
	public String toString() {
		final StringBuilder out = new StringBuilder();

		if (constraintCount == 0) {
			out.append("No constraints on the next state.");
		} else {
			for (final Variable variable : mDefinedVariables) {
				for (final Constraint constraint : mConstraints.getOrDefault(variable, new ArrayList<>())) {
					out.append(constraint.toString()).append("\n");
				}

				for (final Arc arc : mArcs.getOrDefault(variable, new ArrayList<>())) {
					out.append(arc.toString()).append("\n");
				}
			}
		}

		return out.toString().stripTrailing();
	}

	public static BooleanTerm solveForSubject(final BooleanTerm term, final Variable subject) {
		if (!term.getVariables().contains(subject)) {
			return null;
		}

		final ExecutionTerm[] subTerms;
		RelationSymbol relation;

		switch (term) {
		case final GreaterEqualTerm geq:
			subTerms = Util.fillArray(geq.getSubTerms(), new IntegerTerm[2]);
			relation = RelationSymbol.GEQ;
			break;
		case final GreaterTerm gt:
			subTerms = Util.fillArray(gt.getSubTerms(), new IntegerTerm[2]);
			relation = RelationSymbol.GREATER;
			break;
		case final LessEqualTerm leq:
			subTerms = Util.fillArray(leq.getSubTerms(), new IntegerTerm[2]);
			relation = RelationSymbol.LEQ;
			break;
		case final LessTerm lss:
			subTerms = Util.fillArray(lss.getSubTerms(), new IntegerTerm[2]);
			relation = RelationSymbol.LESS;
			break;
		case final EqualsTerm eq:
			subTerms = Util.fillArray(eq.getSubTerms(), new ExecutionTerm[2]);
			relation = RelationSymbol.EQ;
			break;
		case final DistinctTerm neq:
			subTerms = Util.fillArray(neq.getSubTerms(), new ExecutionTerm[2]);
			relation = RelationSymbol.DISTINCT;
			break;
		default:
			return null;
		}

		// Term that contains the variable
		ExecutionTerm varContainer;
		// Term that is equivalent to the term that contains the variable
		ExecutionTerm otherSide;

		final boolean zeroContains = subTerms[0].containsVariable(subject);
		final boolean oneContains = subTerms[1].containsVariable(subject);
		if (zeroContains && !oneContains) {
			varContainer = subTerms[0];
			otherSide = subTerms[1];
		} else if (!zeroContains && oneContains) {
			varContainer = subTerms[1];
			otherSide = subTerms[0];
			relation = relation.swapParameters();
		} else {
			// variable appears on both or neither side
			return null;
		}

		switch (relation) {
		case DISTINCT:
		case EQ:
			if (varContainer.returnType == ReturnType.Int) {
				return solveForSubjectEqualityInt((IntegerTerm) varContainer, (IntegerTerm) otherSide, subject,
						relation);
			}
			return solveForSubjectEquality(varContainer, otherSide, subject, relation);
		case GEQ:
		case GREATER:
		case LEQ:
		case LESS:
			return solveForSubjectCompared((IntegerTerm) varContainer, (IntegerTerm) otherSide, subject, relation);
		default:
			return null;
		}
	}

	public static BooleanTerm solveForSubjectEqualityInt(IntegerTerm varContainer, IntegerTerm otherSide,
			final Variable subject, final RelationSymbol relation) {
		while (!varContainer.equals(subject.getTerm())) {
			switch (varContainer) {
			case final AdditionTerm at:
				// otherSide = term + term + ...
				// rewrite to
				// term + term + ... = otherside - term - term ...
				final ArrayList<IntegerTerm> subtractionTerms = new ArrayList<>();
				subtractionTerms.add(otherSide);
				final ArrayList<IntegerTerm> remainingTerms = new ArrayList<>();

				for (final IntegerTerm addedTerm : at.getSubTerms()) {
					if (addedTerm.containsVariable(subject)) {
						remainingTerms.add(addedTerm);
					} else {
						subtractionTerms.add(addedTerm);
					}
				}

				if (remainingTerms.size() == 1) {
					// only one sub term did not contain the variable
					// => varContainer = otherside - term - term - ...
					varContainer = remainingTerms.get(0);
				} else {
					// => varContainerA + varContainerB + ... = otherside - term - term - ...
					// more than one variable TODO
					return null;
				}
				otherSide = new SubtractionTerm(
						Util.fillArray(subtractionTerms, new IntegerTerm[subtractionTerms.size()]));
				break;
			case final SubtractionTerm st:
				// simplify to AdditionTerm, then use existing implementation in next iteration.
				varContainer = st.simplify();
				break;
			case final NegationTerm nt:
				// -varContainer = otherSide
				// becomes
				// varContainer = -otherSide
				varContainer = nt.getSubTerms().get(0);
				otherSide = otherSide.negate().simplify();
				break;
			default:
				return null;
			}
		}

		if (!varContainer.equals(subject.getTerm())) {
			return null;
		}

		IntegerTerm otherSideTemp = otherSide.simplify();
		while (!otherSideTemp.equals(otherSide)) {
			otherSide = otherSideTemp;
			otherSideTemp = otherSideTemp.simplify();
		}

		switch (relation) {
		case EQ:
			return new EqualsTerm(varContainer, otherSide);
		case DISTINCT:
			return new DistinctTerm(varContainer, otherSide);
		default:
			return null;
		}
	}

	public static BooleanTerm solveForSubjectCompared(IntegerTerm varContainer, IntegerTerm otherSide,
			final Variable subject, RelationSymbol relation) {
		while (!varContainer.equals(subject.getTerm())) {
			switch (varContainer) {
			case final AdditionTerm at:
				// otherSide = term + term + ...
				// rewrite to
				// term + term + ... = otherside - term - term ...
				final ArrayList<IntegerTerm> subtractionTerms = new ArrayList<>();
				subtractionTerms.add(otherSide);
				final ArrayList<IntegerTerm> remainingTerms = new ArrayList<>();

				for (final IntegerTerm addedTerm : at.getSubTerms()) {
					if (addedTerm.containsVariable(subject)) {
						remainingTerms.add(addedTerm);
					} else {
						subtractionTerms.add(addedTerm);
					}
				}

				if (remainingTerms.size() == 1) {
					// only one sub term did not contain the variable
					// => varContainer = otherside - term - term - ...
					varContainer = remainingTerms.get(0);
				} else {
					// => varContainerA + varContainerB + ... = otherside - term - term - ...
					// more than one variable TODO
					return null;
				}
				otherSide = new SubtractionTerm(
						Util.fillArray(subtractionTerms, new IntegerTerm[subtractionTerms.size()]));
				break;
			case final SubtractionTerm st:
				// simplify to AdditionTerm, then use existing implementation in next iteration.
				varContainer = st.simplify();
				break;
			case final NegationTerm nt:
				// -varContainer < otherSide
				// becomes
				// varContainer > -otherSide
				varContainer = nt.getSubTerms().get(0);
				otherSide = otherSide.negate().simplify();
				relation = relation.swapParameters();
				break;
			default:
				return null;
			}
		}

		if (!varContainer.equals(subject.getTerm())) {
			return null;
		}

		IntegerTerm otherSideTemp = otherSide.simplify();
		while (!otherSideTemp.equals(otherSide)) {
			otherSide = otherSideTemp;
			otherSideTemp = otherSideTemp.simplify();
		}

		switch (relation) {
		case GEQ:
			return new GreaterEqualTerm(varContainer, otherSide);
		case GREATER:
			return new GreaterTerm(varContainer, otherSide);
		case LEQ:
			return new LessEqualTerm(varContainer, otherSide);
		case LESS:
			return new LessTerm(varContainer, otherSide);
		default:
			return null;
		}
	}

	public static BooleanTerm solveForSubjectEquality(final ExecutionTerm varContainer, final ExecutionTerm otherSide,
			final Variable subject, final RelationSymbol relation) {
		if (!varContainer.equals(subject.getTerm())) {
			return null;
		}

		switch (relation) {
		case EQ:
			return new EqualsTerm(varContainer, otherSide);
		case DISTINCT:
			return new DistinctTerm(varContainer, otherSide);
		default:
			return null;
		}
	}
}
