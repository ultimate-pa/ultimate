package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctConjunction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonCalculator;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.ParametricOctMatrix;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * @author Jill Enke (enkei@informatik.uni-freiburg.de)
 *
 */
public class FastUPRFormulaBuilder {

	private final FastUPRUtils mUtils;
	private final ManagedScript mManagedScript;
	private final Script mScript;
	private final OctagonCalculator mCalculator;
	private final OctagonTransformer mTransformer;
	private final FastUPRTermTransformer mTermTransformer;

	public FastUPRFormulaBuilder(FastUPRUtils utils, ManagedScript mgdScript, OctagonCalculator calc,
			OctagonTransformer transformer) {
		mUtils = utils;
		mManagedScript = mgdScript;
		mScript = mgdScript.getScript();
		mCalculator = calc;
		mTransformer = transformer;
		mTermTransformer = new FastUPRTermTransformer(mScript);
	}

	private UnmodifiableTransFormula buildTransFormula(Term term, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars, TermVariable parametricVar) {
		final Term withoutInt = mTermTransformer.transformToInt(term);
		final ModifiableTransFormula modFormula = new ModifiableTransFormula(withoutInt);
		for (final IProgramVar p : inVars.keySet()) {
			modFormula.addInVar(p, inVars.get(p));
		}
		for (final IProgramVar p : outVars.keySet()) {
			modFormula.addOutVar(p, outVars.get(p));
		}
		if (parametricVar != null) {
			modFormula.addAuxVars(new HashSet<>(Arrays.asList(parametricVar)));
		}
		return TransFormulaBuilder.constructCopy(mManagedScript, modFormula, Collections.emptySet(),
				Collections.emptySet(), Collections.emptyMap());
	}

	public UnmodifiableTransFormula buildTransFormula(Term term, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		final Term withoutInt = mTermTransformer.transformToInt(term);
		final ModifiableTransFormula modFormula = new ModifiableTransFormula(withoutInt);
		for (final IProgramVar p : inVars.keySet()) {
			modFormula.addInVar(p, inVars.get(p));
		}
		for (final IProgramVar p : outVars.keySet()) {
			modFormula.addOutVar(p, outVars.get(p));
		}
		return TransFormulaBuilder.constructCopy(mManagedScript, modFormula, Collections.emptySet(),
				Collections.emptySet(), Collections.emptyMap());
	}

	public UnmodifiableTransFormula buildTransFormula(OctConjunction conjunction, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		return buildTransFormula(conjunction.toTerm(mManagedScript.getScript()), inVars, outVars);
	}

	public Term buildConsistencyResult(OctConjunction conjunc, int count, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {

		mUtils.output("Returning Consistency Result");
		final ArrayList<Term> orTerms = new ArrayList<>();
		for (int i = 0; i <= count; i++) {
			orTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		final Term result = orTerms.size() > 1 ? mScript.term("or", orTerms.toArray(new Term[0])) : orTerms.get(0);
		return result;
	}

	public Term toExistential(Term term) {
		if (!(term instanceof QuantifiedFormula)) {
			return term;
		}
		final QuantifiedFormula quantTerm = (QuantifiedFormula) term;
		if (quantTerm.getQuantifier() == QuantifiedFormula.EXISTS) {
			return term;
		}
		final Term notTerm = mScript.term("not", quantTerm.getSubformula());
		final Term existentialTerm = mScript.quantifier(QuantifiedFormula.EXISTS, quantTerm.getVariables(), notTerm);
		return mScript.term("not", existentialTerm);
	}

	public Term buildParametricResult(OctConjunction conjunc, int b, ParametricOctMatrix difference,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		// R* := OR(i=0->b-1) (R^i) or EXISTS k>=0. OR(i=0->c-1)
		// (pi(k*difference + sigma(R^b)) ○ R^i

		final ArrayList<Term> firstOrTerms = new ArrayList<>();
		for (int i = 0; i < b; i++) {
			firstOrTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		final Term firstOr = firstOrTerms.size() > 1 ? mScript.term("or", firstOrTerms.toArray(new Term[0]))
				: firstOrTerms.get(0);

		final ArrayList<Term> secondOrTerms = new ArrayList<>();
		final ParametricOctMatrix parametricDiff = difference.multiplyVar("k", mManagedScript);
		for (int i = 0; i < b; i++) {
			secondOrTerms
					.add(getParametricSolutionRightSide(conjunc, b, i, parametricDiff, inVars, outVars, variables));
		}
		final Term secondOr = secondOrTerms.size() > 1 ? mScript.term("or", secondOrTerms.toArray(new Term[0]))
				: secondOrTerms.get(0);
		final Term secondOrQuantified = mScript.quantifier(QuantifiedFormula.EXISTS,
				new TermVariable[] { parametricDiff.getParametricVar() },
				mScript.term("and",
						mScript.term(">=", parametricDiff.getParametricVar(), mScript.decimal(BigDecimal.ZERO)),
						secondOr));
		final Term result = mScript.term("or", firstOr, secondOrQuantified);

		mUtils.output("Returning Parametric Result");
		return result;
	}

	private Term getParametricSolutionRightSide(OctConjunction conjunc, int b, int i,
			ParametricOctMatrix parametricDiff, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars, List<TermVariable> variables) {
		final ParametricOctMatrix rBMatrix = mTransformer
				.getMatrix(mCalculator.sequentialize(conjunc, inVars, outVars, b), variables);
		final ParametricOctMatrix completeMatrix = parametricDiff.add(rBMatrix);
		final OctConjunction firstPart = completeMatrix.toOctConjunction();
		final OctConjunction result = mCalculator.binarySequentialize(firstPart,
				mCalculator.sequentialize(conjunc, inVars, outVars, i), inVars, outVars);

		return result.toTerm(mScript);
	}

	public Term buildPeriodicityResult(OctConjunction conjunc, ParametricOctMatrix difference, int b, int c, int n,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		// R* := OR(i=0->b-1) (R^i) or OR(k=0->n0-1) OR (i=0->c-1)
		// rho(k*difference + sigma(R^b)) ○ R^i

		final ArrayList<Term> firstOrTerms = new ArrayList<>();
		for (int i = 0; i < b; i++) {
			firstOrTerms.add(mCalculator.sequentialize(conjunc, inVars, outVars, i).toTerm(mScript));
		}
		final Term firstOr = firstOrTerms.size() > 1 ? mScript.term("or", firstOrTerms.toArray(new Term[0]))
				: firstOrTerms.get(0);
		final List<Term> outerOrTerms = new ArrayList<>();
		for (int k = 0; k < n; k++) {
			final List<Term> innerOrTerms = new ArrayList<>();
			for (int i = 0; i < c; i++) {
				innerOrTerms.add(getInnerOrTerm(conjunc, b, i, n, difference, inVars, outVars, variables));
			}
			final Term innerOr = innerOrTerms.size() > 1 ? mScript.term("or", innerOrTerms.toArray(new Term[0]))
					: innerOrTerms.get(0);
			outerOrTerms.add(innerOr);
		}
		final Term outerOr = outerOrTerms.size() > 1 ? mScript.term("or", outerOrTerms.toArray(new Term[0]))
				: outerOrTerms.get(0);
		final Term result = mScript.term("or", firstOr, outerOr);

		mUtils.output("Returning Periodicity Result");

		return result;
	}

	private Term getInnerOrTerm(OctConjunction conjunc, int b, int i, int n, ParametricOctMatrix difference,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			List<TermVariable> variables) {
		final ParametricOctMatrix rBMatrix = mTransformer
				.getMatrix(mCalculator.sequentialize(conjunc, inVars, outVars, b), variables);
		final ParametricOctMatrix differenceMultiplied = difference.multiplyConstant(new BigDecimal(n));
		final ParametricOctMatrix completeMatrix = differenceMultiplied.add(rBMatrix);
		final OctConjunction firstPart = completeMatrix.toOctConjunction();
		final OctConjunction result = mCalculator.binarySequentialize(firstPart,
				mCalculator.sequentialize(conjunc, inVars, outVars, i), inVars, outVars);
		return result.toTerm(mScript);
	}

	private Term getIdentityRelation(Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		final ArrayList<Term> terms = new ArrayList<>();
		for (final IProgramVar p : inVars.keySet()) {
			final TermVariable in = inVars.get(p);
			TermVariable out;
			if (outVars.containsKey(p)) {
				out = outVars.get(p);
			} else {
				out = mManagedScript.constructFreshTermVariable(in.getName() + "_out", in.getSort());
				outVars.put(p, out);
			}
			terms.add(mScript.term("=", in, out));
		}
		for (final IProgramVar p : outVars.keySet()) {
			if (!inVars.containsKey(p)) {
				final TermVariable out = outVars.get(p);
				final TermVariable in = mManagedScript.constructFreshTermVariable(out.getName() + "_in", out.getSort());
				inVars.put(p, in);
				terms.add(mScript.term("=", in, out));
			}
		}
		if (terms.isEmpty()) {
			return mScript.term("true");
		} else if (terms.size() == 1) {
			return terms.get(0);
		}
		final Term identityTerm = mScript.term("and", terms.toArray(new Term[0]));
		return identityTerm;
	}

	public Term getExitEdgeResult(UnmodifiableTransFormula exitEdgeFormula, Term t,
			Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars) {
		final Term identityRelation = getIdentityRelation(inVars, outVars);
		final Term loop = mScript.term("or", identityRelation, t);

		final Term exitTerm = buldExitRelation(inVars, outVars, exitEdgeFormula);

		return mScript.term("and", loop, exitTerm);
	}

	private Term buldExitRelation(Map<IProgramVar, TermVariable> inVars, Map<IProgramVar, TermVariable> outVars,
			UnmodifiableTransFormula exitEdgeFormula) {
		Term exitTerm = exitEdgeFormula.getFormula();

		for (final Entry<IProgramVar, TermVariable> e : exitEdgeFormula.getInVars().entrySet()) {
			final TermVariable outVar = outVars.get(e.getKey());
			exitTerm = mTermTransformer.replaceVar(exitTerm, e.getValue(), outVar);
		}

		return exitTerm;
	}

}
