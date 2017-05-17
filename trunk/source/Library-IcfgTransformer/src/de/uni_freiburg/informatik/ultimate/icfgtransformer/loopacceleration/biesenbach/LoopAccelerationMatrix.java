/*
 * Copyright (C) 2017 Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;

/**
 *
 * @author Ben Biesenbach (ben.biesenbach@gmx.de)
 *
 * @param <INLOC>
 */
public class LoopAccelerationMatrix<INLOC extends IcfgLocation> {

	private final MatrixBB mMatrix;
	private final UnmodifiableTransFormula mOriginalTransFormula;
	private final ManagedScript mMgScript;
	private List<Integer> mOpen = new ArrayList<>();
	private List<Integer> mNewVectors = new ArrayList<>();

	public LoopAccelerationMatrix(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		final CfgSmtToolkit cfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = cfgSmtToolkit.getManagedScript();

		mMgScript.lock(this);
		mMgScript.push(this, 1);

		mOriginalTransFormula =
				originalIcfg.getInitialNodes().iterator().next().getOutgoingEdges().iterator().next().getTransformula();
		mMatrix = new MatrixBB(mOriginalTransFormula.getInVars().size(), logger);

		test(logger);
		fillMatrix(logger, originalIcfg, services);
		mMatrix.print();

		mMgScript.pop(this, 1);
		mMgScript.unlock(this);
	}

	private void fillMatrix(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		// n = 0 (siehe matrixbb.init())
		// n = 1
		final int matrixSize = mOriginalTransFormula.getInVars().size();
		for (int i = matrixSize; i < matrixSize * 2; i++) {
			mOpen.add(i);
		}
		findInitVector(logger, originalIcfg, services);
		logger.info("open: " + mOpen.isEmpty());
		while (!mNewVectors.isEmpty() && !mOpen.isEmpty()) {
			final List<Integer> open = new ArrayList<>();
			final List<Integer> newVectors = new ArrayList<>();
			for (final int vNumber : mOpen) {
				for (final int vNumberOld : mNewVectors) {
					final int[] constI = mMatrix.getVectorInt(vNumberOld).clone();
					final Term[] constT = mMatrix.getVectorTerm(vNumberOld).clone();
					// TODO statt festen Wert mit Variable belegen und L�sung
					// ausgeben lassen
					// val[n] = originalTransFormula.getInVars().values().toArray(newTermVariable[2])[n]
					final Rational one = Rational.valueOf(1, 1);
					constT[vNumber - matrixSize] = one.toTerm(SmtSortUtils.getIntSort(mMgScript));
					constI[vNumber - matrixSize] = 1;
					final Term m = mMgScript.getScript().let(
							mOriginalTransFormula.getInVars().values().toArray(new TermVariable[matrixSize]), constT,
							mOriginalTransFormula.getFormula());
					logger.info(m);
					if (SmtUtils.checkSatTerm(mMgScript.getScript(), m).equals(LBool.SAT)) {
						newVectors.add(vNumber);
						mMatrix.setVector(vNumber, constI, constT, 1);
					} else {
						open.add(vNumber);
					}
				}
			}
			mOpen = open;
			mNewVectors = newVectors;
		}
		// n = 2
		// TODO Beliebige L�sung mit n = 2

		// TODO Was machen wenn der Algorithmus abbrechen soll/keine L�sung
		// findet?
	}

	private void test(final ILogger logger) {
		logger.info(mOriginalTransFormula.getFormula());
		logger.info(mOriginalTransFormula.getClosedFormula());
		final Script script = mMgScript.getScript();
		final Term zero = Rational.valueOf(0, 1).toTerm(SmtSortUtils.getIntSort(script));

		final List<Entry<IProgramVar, TermVariable>> invars =
				mOriginalTransFormula.getInVars().entrySet().stream().collect(Collectors.toList());

		final int firstN = mOriginalTransFormula.getInVars().size() - 1;
		final Entry<IProgramVar, TermVariable> last = invars.get(firstN);

		final Map<Term, Term> substitution = new HashMap<>();
		invars.stream().limit(firstN).forEach(invar -> substitution.put(invar.getValue(), zero));
		substitution.put(last.getValue(), last.getKey().getDefaultConstant());
		final Substitution sub = new Substitution(mMgScript, substitution);
		Term transformedTerm = sub.transform(mOriginalTransFormula.getFormula());
		transformedTerm =
				script.term("and", transformedTerm, script.term("distinct", last.getKey().getDefaultConstant(), zero));

		logger.info(transformedTerm);
		logger.info("Asking for " + last.getKey().getDefaultConstant());

		script.push(1);
		try {
			final LBool result = checkSat(script, transformedTerm);

			if (result == LBool.SAT) {
				final Map<Term, Term> termvar2value =
						SmtUtils.getValues(script, Collections.singleton(last.getKey().getDefaultConstant()));
				logger.info(termvar2value);
			}
		} finally {
			script.pop(1);
		}
	}

	public static LBool checkSat(final Script script, Term term) {
		final TermVariable[] vars = term.getFreeVars();
		final Term[] values = new Term[vars.length];
		for (int i = 0; i < vars.length; i++) {
			values[i] = termVariable2constant(script, vars[i]);
		}
		term = script.let(vars, values, term);
		LBool result = script.assertTerm(term);
		if (result == LBool.UNKNOWN) {
			result = script.checkSat();
		}
		return result;
	}

	private static Term termVariable2constant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort resultSort = tv.getSort();
		script.declareFun(name, Script.EMPTY_SORT_ARRAY, resultSort);
		return script.term(name);
	}

	private void findInitVector(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		// TODO entweder "alle gleich 0" oder "keiner gleich 0"
		// nullvektor
		final int matrixSize = mOriginalTransFormula.getInVars().size();
		final Term[] constT = new Term[matrixSize];
		final int[] constI = new int[matrixSize];
		for (int n = 0; n < matrixSize; n++) {
			final Rational one = Rational.valueOf(0, 1);
			constT[n] = one.toTerm(SmtSortUtils.getIntSort(mMgScript));
			constI[n] = 0;
		}
		final Term m = mMgScript.getScript().let(
				mOriginalTransFormula.getInVars().values().toArray(new TermVariable[matrixSize]), constT,
				mOriginalTransFormula.getFormula());
		if (SmtUtils.checkSatTerm(mMgScript.getScript(), m).equals(LBool.SAT)) {
			mNewVectors.add(matrixSize * 2);
			mMatrix.setVector(matrixSize * 2, constI, constT, 1);
		}
	}

	private void DD(final ILogger logger, final IIcfg<INLOC> originalIcfg, final IUltimateServiceProvider services) {

		// DD: Some code snippets
		final CfgSmtToolkit cfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		final ManagedScript mgdScript = cfgSmtToolkit.getManagedScript();

		mgdScript.lock(this);
		final Term formula = null;
		final LBool result = SmtUtils.checkSatTerm(mgdScript.getScript(), formula);
		mgdScript.push(this, 1);
		// ...
		final Rational one = Rational.valueOf(1, 1);
		final Term oneTerm = one.toTerm(SmtSortUtils.getIntSort(mMgScript));
		mgdScript.assertTerm(this, oneTerm);
		final Model model = mgdScript.getScript().getModel();

		final SimplificationTechnique simpl = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConvTech = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		final PredicateTransformer<Term, IPredicate, TransFormula> ptf = new PredicateTransformer<>(
				mgdScript, new TermDomainOperationProvider(services, mgdScript));

		final BasicPredicateFactory predFac =
				new BasicPredicateFactory(services, mgdScript, cfgSmtToolkit.getSymbolTable(), simpl, xnfConvTech);

		final UnmodifiableTransFormula tf = null;
		final IPredicate pre = predFac.newPredicate(mgdScript.getScript().term("true"));
		final Term postTerm = ptf.strongestPostcondition(pre, tf);
		final IPredicate post = predFac.newPredicate(postTerm);

		mgdScript.pop(this, 1);
		mgdScript.unlock(this);
	}
}
