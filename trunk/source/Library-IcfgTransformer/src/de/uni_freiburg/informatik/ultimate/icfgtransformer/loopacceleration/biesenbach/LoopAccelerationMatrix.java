package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;

public class LoopAccelerationMatrix<INLOC extends IcfgLocation> {

	private MatrixBB mMatrix;
	private UnmodifiableTransFormula mOriginalTransFormula;
	private ManagedScript mMgScript;
	private List<Integer> mOpen = new ArrayList<>();
	private List<Integer> mNewVectors = new ArrayList<>();

	public LoopAccelerationMatrix(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		final CfgSmtToolkit cfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = cfgSmtToolkit.getManagedScript();

		mMgScript.lock(this);
		mMgScript.push(this, 1);

		mOriginalTransFormula = originalIcfg.getInitialNodes().iterator().next().getOutgoingEdges().iterator().next()
				.getTransformula();
		mMatrix = new MatrixBB(mOriginalTransFormula.getInVars().size(), logger);

		fillMatrix(logger, originalIcfg, services);
		mMatrix.print();

		mMgScript.pop(this, 1);
		mMgScript.unlock(this);
	}

	private void fillMatrix(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		// n = 0 (siehe matrixbb.init())
		// n = 1
		int matrixSize = mOriginalTransFormula.getInVars().size();
		for (int i = matrixSize; i < matrixSize * 2; i++) {
			mOpen.add(i);
		}
		findInitVector(logger, originalIcfg, services);
		logger.info("open: " + mOpen.isEmpty());
		while (!mNewVectors.isEmpty() && !mOpen.isEmpty()) {
			List<Integer> open = new ArrayList<>();
			List<Integer> newVectors = new ArrayList<>();
			for (int vNumber : mOpen) {
				for (int vNumberOld : mNewVectors) {
					int[] constI = mMatrix.getVectorInt(vNumberOld).clone();
					Term[] constT = mMatrix.getVectorTerm(vNumberOld).clone();
					// TODO statt festen Wert mit Variable belegen und Lösung
					// ausgeben lassen
					// val[n] = originalTransFormula.getInVars().values().toArray(newTermVariable[2])[n]
					final Rational one = Rational.valueOf(1, 1);
					constT[vNumber - matrixSize] = one.toTerm(mMgScript.getScript().sort("Int"));
					constI[vNumber - matrixSize] = 1;
					Term m = mMgScript.getScript().let(
							mOriginalTransFormula.getInVars().values().toArray(new TermVariable[matrixSize]), constT,
							mOriginalTransFormula.getFormula());
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
		// TODO Beliebige Lösung mit n = 2

		// TODO Was machen wenn der Algorithmus abbrechen soll/keine Lösung
		// findet?
	}

	private void findInitVector(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final IUltimateServiceProvider services) {
		// TODO entweder "alle gleich 0" oder "keiner gleich 0"
		// nullvektor
		int matrixSize = mOriginalTransFormula.getInVars().size();
		Term[] constT = new Term[matrixSize];
		int[] constI = new int[matrixSize];
		for (int n = 0; n < matrixSize; n++) {
			final Rational one = Rational.valueOf(0, 1);
			constT[n] = one.toTerm(mMgScript.getScript().sort("Int"));
			constI[n] = 0;
		}
		Term m = mMgScript.getScript().let(
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
		final ManagedScript mgScript = cfgSmtToolkit.getManagedScript();

		mgScript.lock(this);
		final Term formula = null;
		final LBool result = SmtUtils.checkSatTerm(mgScript.getScript(), formula);
		mgScript.push(this, 1);
		// ...
		final Rational one = Rational.valueOf(1, 1);
		final Term oneTerm = one.toTerm(mgScript.getScript().sort("Int"));
		mgScript.assertTerm(this, oneTerm);
		final Model model = mgScript.getScript().getModel();

		final SimplificationTechnique simpl = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConvTech = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		final PredicateTransformer ptf = new PredicateTransformer(services, mgScript, simpl, xnfConvTech);

		final BasicPredicateFactory predFac = new BasicPredicateFactory(services, mgScript,
				cfgSmtToolkit.getSymbolTable(), simpl, xnfConvTech);

		final UnmodifiableTransFormula tf = null;
		final IPredicate pre = predFac.newPredicate(mgScript.getScript().term("true"));
		final Term postTerm = ptf.strongestPostcondition(pre, tf);
		final IPredicate post = predFac.newPredicate(postTerm);

		mgScript.pop(this, 1);
		mgScript.unlock(this);
	}
}
