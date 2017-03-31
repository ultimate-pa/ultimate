/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.awt.List;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.logging.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct.OctagonConcatination;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctMatrix;

public class FastUPRCore<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>{

	private final Term mRelation;
	private final UnmodifiableTransFormula mFormula;
	private final UnmodifiableTransFormula mResult;
	private final ILogger mLogger;
	private final FastUPRUtils mUtils;
	private ILocationFactory<INLOC, OUTLOC> mReplacementVarFactory;
	
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	
	public FastUPRCore(UnmodifiableTransFormula formula,
			ILocationFactory<INLOC, OUTLOC> factory,
			ManagedScript managedScript,
			ILogger logger,
			IUltimateServiceProvider services) throws Exception {
		mLogger = logger;
		mFormula = formula;
		mRelation = formula.getFormula();
		mUtils = new FastUPRUtils(logger);
		
		mLogger.debug(mFormula.toString());
		mLogger.debug(mRelation.toString());
		
		mServices = services;
		mManagedScript = managedScript;
		mReplacementVarFactory = factory;
		if(!isOctagon(mRelation, mManagedScript.getScript())) mResult = mFormula;
		else mResult = prefixLoop();
	}
	
	
	
	
	private boolean isOctagon(Term relation, Script script) throws NotAffineException {
		
		Term cnfRelation = SmtUtils.toCnf(mServices, mManagedScript, relation,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		
		mLogger.debug("CNF");
		mLogger.debug(cnfRelation.toString());
		
		OctagonDetector detector = new OctagonDetector(mLogger);
		HashSet<Term> subTerms = detector.getConcatSubTerms(cnfRelation);
		ArrayList<Term> octTerms = new ArrayList<>();
		
		mLogger.debug("Term count:" + subTerms.size());
			
		detector.clearChecked();
		
		for (Term t : subTerms) {
			final AffineRelation affine = new AffineRelation(script, t);
			t = affine.positiveNormalForm(script);
			mLogger.debug("Term as Positive Normal Form");
			mLogger.debug(t.toString());
			detector.isOctagonTerm(t);
			if(!detector.isOctagon()) return false;
			octTerms.add(t);
		}
		
		OctagonTransformer transformer = new OctagonTransformer(mLogger);
		
		OctagonConcatination oct = transformer.transform(octTerms);
		
		return true;
	}

	private UnmodifiableTransFormula prefixLoop() {
		int b = 0;
		boolean resultFound = false;
		while(!resultFound) {
			periodLoop(b++);
			if (b > 100) resultFound = true;
		}
		
		return null;
	}
	
	private void periodLoop(int b) {
		for (int c = 0; c <= b; c++) {
			ConsistencyChecker checker = new ConsistencyChecker(mUtils, mLogger, mManagedScript, mServices, mFormula, b, c);
			if(checker.isSuccess()) {
				checker.getResult();
				return;
			} else {
				return;
			}
			
		}
	}
}
