/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.BvToIntTransformation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionsAndAxioms;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationManager;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * {@link ITransformulaTransformer} that can transform each {@link TransFormula} separately (without knowing the whole
 * {@link IIcfg}. TODO 20211228 Matthias: This class is a workaround for running the BvToInt translation We will
 * generalize this later.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class BvToIntTransformulaTransformer implements ITransformulaTransformer {

	private final ManagedScript mMgdScript;
	private final Function<Sort, Sort> mSortTranslation;
	// private CfgSmtToolkit csToolkit
	private HashRelation<String, IProgramNonOldVar> mNewModifiableGlobals;
	private VariableTranslation mVarTrans;
	private IIcfgSymbolTable mNewSymbolTable;
	private final ConstraintsForBitwiseOperations mCfbo;
	private final boolean mNutzTransformation;

	/**
	 * Default constructor using a sequence of {@link TransitionPreprocessor}s.
	 *
	 * @param transitionPreprocessors
	 *            A {@link List} of {@link TransitionPreprocessor}s that should be used in that order.
	 * @param managedScript
	 *            A {@link ManagedScript} instance used to convert {@link UnmodifiableTransFormula}s to
	 *            {@link ModifiableTransFormula}s and back.
	 * @param cfbo
	 * @param replacementVarFactory
	 *            A {@link ReplacementVarFactory} instance.
	 */
	public BvToIntTransformulaTransformer(final ManagedScript managedScript, final ConstraintsForBitwiseOperations cfbo,
			final boolean useNutzTransformation) {
		mMgdScript = Objects.requireNonNull(managedScript);
		mSortTranslation = x -> BvToIntTransformation.bvToIntSort(mMgdScript, x);
		mCfbo = cfbo;
		mNutzTransformation = useNutzTransformation;
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		if (!tf.getBranchEncoders().isEmpty()) {
			throw new UnsupportedOperationException("Branch encoders");
		}
		final Map<Term, Term> translationMap = new HashMap<>(mVarTrans.getIProgramConstTermMap());
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar newProgramVar = mVarTrans.translateProgramVar(entry.getKey());
			final boolean isInVarAndOutVar = (entry.getValue() == tf.getOutVars().get(entry.getKey()));
			String suffix;
			if (isInVarAndOutVar) {
				suffix = "InAndOut";
			} else {
				suffix = "In";
			}
			final TermVariable tv = mMgdScript.constructFreshTermVariable(
					newProgramVar.getTermVariable().getName() + suffix, newProgramVar.getSort());
			inVars.put(newProgramVar, tv);
			if (isInVarAndOutVar) {
				outVars.put(newProgramVar, tv);
			}
			translationMap.put(tf.getInVars().get(entry.getKey()), tv);
		}
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final boolean isInVarAndOutVar = (entry.getValue() == tf.getInVars().get(entry.getKey()));
			if (isInVarAndOutVar) {
				// variable was already added above
				continue;
			}
			final IProgramVar newProgramVar = mVarTrans.translateProgramVar(entry.getKey());
			final String suffix = "Out";
			final TermVariable tv = mMgdScript.constructFreshTermVariable(
					newProgramVar.getTermVariable().getName() + suffix, newProgramVar.getSort());
			outVars.put(newProgramVar, tv);
			translationMap.put(tf.getOutVars().get(entry.getKey()), tv);
		}
		final Set<IProgramConst> newProgramConstants;
		if (tf.getNonTheoryConsts().isEmpty()) {
			newProgramConstants = null;
		} else {
			newProgramConstants = tf.getNonTheoryConsts().stream().map(x -> mVarTrans.translateProgramConst(x))
					.collect(Collectors.toSet());
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, tf.getNonTheoryConsts().isEmpty(),
				newProgramConstants, true, null, false);
		for (final TermVariable auxVar : tf.getAuxVars()) {
			final TermVariable newAuxVar = mMgdScript.constructFreshTermVariable(auxVar.getName() + "Int",
					mSortTranslation.apply(auxVar.getSort()));
			translationMap.put(auxVar, newAuxVar);
			tfb.addAuxVar(newAuxVar);
		}
		final Term term = tf.getFormula();
		final Triple<Term, Set<TermVariable>, Boolean> translated = translateTerm(mMgdScript, translationMap, term);
		for (final TermVariable newAuxVar : translated.getSecond()) {
			tfb.addAuxVar(newAuxVar);
		}
		tfb.setFormula(translated.getFirst());
		tfb.setInfeasibility(tf.isInfeasible());
		final UnmodifiableTransFormula resultTf = tfb.finishConstruction(mMgdScript);
		return new TransformulaTransformationResult(resultTf, translated.getThird());
	}

	private Triple<Term, Set<TermVariable>, Boolean> translateTerm(final ManagedScript mgdScript,
			final Map<Term, Term> translationMap, final Term term) {
		final TranslationManager translationManager = new TranslationManager(mgdScript, mCfbo, mNutzTransformation);
		translationManager.setReplacementVarMaps(new LinkedHashMap<>(translationMap));
		final Triple<Term, Set<TermVariable>, Boolean> translated = translationManager.translateBvtoInt(term);
		return translated;
	}

	@Override
	public AxiomTransformationResult transform(final IPredicate oldAxioms) {
		if (!oldAxioms.getFuns().isEmpty()) {
			throw new UnsupportedOperationException(String.format(
					"Cannot yet translate axioms but CFG has axioms that contain %s uninterpreted function symbols",
					oldAxioms.getFuns().size()));
		}

		final Triple<Term, Set<TermVariable>, Boolean> result =
				translateTerm(mMgdScript, new HashMap<>(mVarTrans.getIProgramConstTermMap()), oldAxioms.getFormula());
		// Quantify auxiliary variables
		final Term withoutAuxVars = SmtUtils.quantifier(mMgdScript.getScript(), QuantifiedFormula.EXISTS,
				result.getSecond(), result.getFirst());
		final IPredicate transformedAxiom =
				new BasicPredicate(0, withoutAuxVars, Collections.emptySet(), oldAxioms.getFuns(), withoutAuxVars);
		final boolean isOverappoximation = result.getThird();
		return new AxiomTransformationResult(transformedAxiom, isOverappoximation);
	}

	@Override
	public String getName() {
		return "BvToInt";

	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		final CfgSmtToolkit csToolkit = icfg.getCfgSmtToolkit();
		mVarTrans = new VariableTranslation("Int");
		mNewModifiableGlobals = constructNewProc2Globals(csToolkit.getModifiableGlobalsTable().getProcToGlobals(),
				mMgdScript, mMgdScript, mVarTrans);
		mNewSymbolTable = constructNewSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures(), mVarTrans);
		// csToolkit = constructNewCfgSmtToolkit(icfg.getCfgSmtToolkit(), mMgdScript, mMgdScript);

	}

	private CfgSmtToolkit constructNewCfgSmtToolkit(final CfgSmtToolkit csToolkit, final ManagedScript oldMgdScript,
			final ManagedScript newMgdScript) {
		final VariableTranslation varTrans = new VariableTranslation("Int");
		final HashRelation<String, IProgramNonOldVar> proc2globals = constructNewProc2Globals(
				csToolkit.getModifiableGlobalsTable().getProcToGlobals(), oldMgdScript, newMgdScript, varTrans);
		final ModifiableGlobalsTable modifiableGlobalsTable = new ModifiableGlobalsTable(proc2globals);
		final IIcfgSymbolTable symbolTable =
				constructNewSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures(), varTrans);
		final Map<String, List<ILocalProgramVar>> inParams = constructNewParams(csToolkit.getInParams(), varTrans);
		final Map<String, List<ILocalProgramVar>> outParams = constructNewParams(csToolkit.getOutParams(), varTrans);
		final SmtFunctionsAndAxioms smtFunctionsAndAxioms = null;
		return new CfgSmtToolkit(modifiableGlobalsTable, newMgdScript, symbolTable, csToolkit.getProcedures(), inParams,
				outParams, csToolkit.getIcfgEdgeFactory(), csToolkit.getConcurrencyInformation(),
				smtFunctionsAndAxioms);
	}

	private static Map<String, List<ILocalProgramVar>> constructNewParams(
			final Map<String, List<ILocalProgramVar>> inParams, final VariableTranslation variableTranslation) {
		final Map<String, List<ILocalProgramVar>> result = new HashMap<>();
		for (final Entry<String, List<ILocalProgramVar>> entry : inParams.entrySet()) {
			final List<ILocalProgramVar> newList = entry.getValue().stream()
					.map(x -> variableTranslation.getOrConstruct(x)).collect(Collectors.toList());
			result.put(entry.getKey(), newList);
		}
		return result;
	}

	private static IIcfgSymbolTable constructNewSymbolTable(final IIcfgSymbolTable symbolTable,
			final Set<String> procedures, final VariableTranslation varTrans) {
		final DefaultIcfgSymbolTable result = new DefaultIcfgSymbolTable();
		for (final IProgramConst c : symbolTable.getConstants()) {
			result.add(varTrans.getOrConstruct(c));
		}
		for (final IProgramNonOldVar g : symbolTable.getGlobals()) {
			result.add(varTrans.getOrConstruct(g));
		}
		for (final String proc : procedures) {
			for (final ILocalProgramVar l : symbolTable.getLocals(proc)) {
				result.add(varTrans.getOrConstruct(l));
			}
		}
		return result;
	}

	private static HashRelation<String, IProgramNonOldVar> constructNewProc2Globals(
			final HashRelation<String, IProgramNonOldVar> procToGlobals, final ManagedScript oldMgdScript,
			final ManagedScript newMgdScript, final VariableTranslation variableTranslation) {
		final HashRelation<String, IProgramNonOldVar> result = new HashRelation<>();
		for (final Entry<String, HashSet<IProgramNonOldVar>> entry : procToGlobals.entrySet()) {
			for (final IProgramNonOldVar old : entry.getValue()) {
				final IProgramNonOldVar newVar = variableTranslation.getOrConstruct(old);
				result.addPair(entry.getKey(), newVar);
			}

		}
		return result;
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		return mNewModifiableGlobals;
	}

	public Map<Term, Term> getBacktranslationMap() {
		return mVarTrans.getBacktranslationMap();
	}

	public class VariableTranslation {
		private final String mVarSuffix;
		private final ConstructionCache<ILocalProgramVar, ILocalProgramVar> mILocalProgramVarCC;
		private final ConstructionCache<IProgramNonOldVar, IProgramNonOldVar> mIProgramNonOldVarCC;
		private final ConstructionCache<IProgramConst, IProgramConst> mIProgramConstCC;
		private final Map<Term, Term> mBacktranslation;

		public VariableTranslation(final String varSuffix) {
			super();
			mVarSuffix = varSuffix;
			mBacktranslation = new HashMap<>();
			mILocalProgramVarCC = new ConstructionCache<>(new IValueConstruction<ILocalProgramVar, ILocalProgramVar>() {

				@Override
				public ILocalProgramVar constructValue(final ILocalProgramVar oldPv) {
					mMgdScript.lock(this);
					final String newIdentifier = oldPv + mVarSuffix;
					final Sort newSort = mSortTranslation.apply(oldPv.getSort());
					final ILocalProgramVar newPv = ProgramVarUtils.constructLocalProgramVar(newIdentifier,
							oldPv.getProcedure(), newSort, mMgdScript, this);
					mMgdScript.unlock(this);
					mBacktranslation.put(newPv.getTerm(), oldPv.getTerm());
					return newPv;
				}
			});
			mIProgramNonOldVarCC =
					new ConstructionCache<>(new IValueConstruction<IProgramNonOldVar, IProgramNonOldVar>() {

						@Override
						public IProgramNonOldVar constructValue(final IProgramNonOldVar oldPv) {
							mMgdScript.lock(this);
							final String newIdentifier = oldPv + mVarSuffix;
							final Sort newSort = mSortTranslation.apply(oldPv.getSort());
							final IProgramNonOldVar newPv = ProgramVarUtils.constructGlobalProgramVarPair(newIdentifier,
									newSort, mMgdScript, this);
							mMgdScript.unlock(this);
							mBacktranslation.put(newPv.getTerm(), oldPv.getTerm());
							mBacktranslation.put(newPv.getOldVar().getTerm(), oldPv.getOldVar().getTerm());
							return newPv;
						}

					});
			mIProgramConstCC = new ConstructionCache<IProgramConst, IProgramConst>(
					new IValueConstruction<IProgramConst, IProgramConst>() {

						@Override
						public IProgramConst constructValue(final IProgramConst oldPv) {
							final String newIdentifier = oldPv.getIdentifier() + mVarSuffix;
							final Sort newSort = mSortTranslation.apply(oldPv.getSort());
							mMgdScript.declareFun(null, newIdentifier, new Sort[0], newSort);
							final ApplicationTerm newSmtConstant =
									(ApplicationTerm) mMgdScript.term(null, newIdentifier);
							mBacktranslation.put(newSmtConstant, oldPv.getDefaultConstant());
							return new ProgramConst(newIdentifier, newSmtConstant, false);
						}
					});
		}

		public ILocalProgramVar getOrConstruct(final ILocalProgramVar key) {
			return mILocalProgramVarCC.getOrConstruct(key);
		}

		public IProgramNonOldVar getOrConstruct(final IProgramNonOldVar key) {
			return mIProgramNonOldVarCC.getOrConstruct(key);
		}

		public IProgramOldVar getOrConstruct(final IProgramOldVar key) {
			return mIProgramNonOldVarCC.getOrConstruct(key.getNonOldVar()).getOldVar();
		}

		public IProgramConst getOrConstruct(final IProgramConst key) {
			return mIProgramConstCC.getOrConstruct(key);
		}

		public Map<ILocalProgramVar, ILocalProgramVar> getILocalProgramVarMap() {
			return Collections.unmodifiableMap(mILocalProgramVarCC);
		}

		public Map<IProgramNonOldVar, IProgramNonOldVar> getIProgramNonOldVarMap() {
			return Collections.unmodifiableMap(mIProgramNonOldVarCC);
		}

		public Map<IProgramConst, IProgramConst> getIProgramConstMap() {
			return Collections.unmodifiableMap(mIProgramConstCC);
		}

		public Map<Term, Term> getIProgramConstTermMap() {
			return getIProgramConstMap().entrySet().stream().collect(
					Collectors.toMap(x -> x.getKey().getDefaultConstant(), x -> x.getValue().getDefaultConstant()));
		}

		public IProgramVar translateProgramVar(final IProgramVar pv) {
			IProgramVar result;
			if (pv instanceof ILocalProgramVar) {
				result = getILocalProgramVarMap().get(pv);
			} else if (pv instanceof IProgramNonOldVar) {
				result = getIProgramNonOldVarMap().get(pv);
			} else if (pv instanceof IProgramOldVar) {
				result = getIProgramNonOldVarMap().get(((IProgramOldVar) pv).getNonOldVar()).getOldVar();
			} else {
				throw new UnsupportedOperationException(pv.getClass().getSimpleName());
			}
			return result;
		}

		public IProgramConst translateProgramConst(final IProgramConst pc) {
			return getIProgramConstMap().get(pc);
		}

		public Map<Term, Term> getBacktranslationMap() {
			return Collections.unmodifiableMap(mBacktranslation);
		}

	}

}
