package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 *
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class MemlocInitializer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements ITransformulaTransformer {
//		extends IcfgTransitionTransformer<INLOC, OUTLOC> {

	private final IProgramVar mValidArray;

	private final HeapSepSettings mSettings;

	private final MemlocArrayManager mMemlocArrayManager;

	private final ManagedScript mMgdScript;

	private final Set<INLOC> mInitialNodes;

	private final DefaultIcfgSymbolTable mNewSymbolTable;

	public MemlocInitializer(final ILogger logger, final CfgSmtToolkit oldCsToolkit,
//			final String resultName,
//			final Class<OUTLOC> outLocClazz, final IIcfg<INLOC> inputCfg,
//			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final MemlocArrayManager memlocArrayMananger, final IProgramVar validArray,
			final HeapSepSettings settings,
			final Set<INLOC> initialNodes) {
//		super(logger, resultName, outLocClazz, inputCfg, funLocFac, backtranslationTracker);

		mValidArray = validArray;
		mMemlocArrayManager = memlocArrayMananger;

		mSettings = settings;

		mMgdScript = oldCsToolkit.getManagedScript();

		mInitialNodes = initialNodes;

		mNewSymbolTable = new DefaultIcfgSymbolTable(oldCsToolkit.getSymbolTable(), oldCsToolkit.getProcedures());
	}



//	@Override
//	protected IcfgEdge transform(final IcfgEdge oldTransition, final OUTLOC newSource, final OUTLOC newTarget) {
	@Override
	public TransforumlaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldTransition,
			final UnmodifiableTransFormula tf) {

		final Script script = mMgdScript.getScript();

//		if (!mInputIcfg.getInitialNodes().contains(oldTransition.getSource())) {
		if (!mInitialNodes.contains(oldTransition.getSource())) {
			// not an initial transition, do nothing
//			return super.transform(oldTransition, newSource, newTarget);
			return new TransforumlaTransformationResult(tf);
		}

		/*
		 * we have an initial edge --> add the initialization code to the transition
		 *  steps:
		 *  <li> add a conjunct with equalities l_x_frz = lit_l_x_frz (l means a location) to the Transformula's
		 *    formula
		 *  <li> add all l_x_frz as assigned vars to the invars/outvars
		 */
		final UnmodifiableTransFormula oldTransformula = oldTransition.getTransformula();

		final ComputeInitializingTerm cit =
				new ComputeInitializingTerm(mMemlocArrayManager, mValidArray, oldTransformula, mSettings);

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(oldTransformula.getInVars());
		newInVars.putAll(cit.getFreezeVarInVars());
		for (final IProgramVar iv : cit.getFreezeVarInVars().keySet()) {
			if (iv instanceof IProgramOldVar) {
				continue;
			}
			mNewSymbolTable.add(iv);
		}

		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(oldTransformula.getOutVars());
		newOutVars.putAll(cit.getFreezeVarOutVars());
		for (final IProgramVar iv : cit.getFreezeVarOutVars().keySet()) {
			if (iv instanceof IProgramOldVar) {
				continue;
			}
			mNewSymbolTable.add(iv);
		}

		/*
		 * Note that the symbol table will be automatically updated with the new constants by the
		 *  TransformedIcfgBuilder (in its .finish() method).
		 */
		final Set<IProgramConst> newNonTheoryConstants = DataStructureUtils.union(
				oldTransformula.getNonTheoryConsts(),
				new HashSet<>(mMemlocArrayManager.getMemLocLits()));

		final TransFormulaBuilder newTfBuilder = new TransFormulaBuilder(
				newInVars, newOutVars, newNonTheoryConstants.isEmpty(), newNonTheoryConstants,
				oldTransformula.getBranchEncoders().isEmpty(), oldTransformula.getBranchEncoders(),
				oldTransformula.getAuxVars().isEmpty());

		// TODO: do we need to lock the mgdscript here??
		/*
		 * conjoin the original transformula with the initializing term
		 */
		final Term newFormula = SmtUtils.and(script, oldTransformula.getFormula(), cit.getInitializingTerm());

		newTfBuilder.setFormula(newFormula);
		newTfBuilder.setInfeasibility(oldTransformula.isInfeasible());
		newTfBuilder.addAuxVarsButRenameToFreshCopies(oldTransformula.getAuxVars(), mMgdScript);

		final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);

//		return super.transform(oldTransition, newSource, newTarget, newTransformula);
		return new TransforumlaTransformationResult(newTransformula);
	}

	class ComputeInitializingTerm {

		// result fields
		private Term mInitializingTerm;
		private Map<IProgramVar, TermVariable> mMemlocInVars;
		private Map<IProgramVar, TermVariable> mMemlocOutVars;

		private final HeapSepSettings mSettings;

		ComputeInitializingTerm(final MemlocArrayManager memlocArrayManager,
				final IProgramVar validArray, final UnmodifiableTransFormula originalTransFormula,
				final HeapSepSettings settings) {
			mSettings = Objects.requireNonNull(settings);
			computeInitializingTerm(Objects.requireNonNull(memlocArrayManager),
					Objects.requireNonNull(validArray),
					Objects.requireNonNull(originalTransFormula));
		}

		private void computeInitializingTerm(final MemlocArrayManager memlocArrayManager,
				final IProgramVar validArray, final UnmodifiableTransFormula originalTransFormula) {
			mMemlocInVars = new HashMap<>();
			mMemlocOutVars = new HashMap<>();


			TermVariable validArrayTv = originalTransFormula.getOutVars().get(validArray);
			if (validArrayTv == null) {
				// originalTransFormula does not constrain valid
				assert originalTransFormula.getInVars().get(validArray) == null : "#valid is havocced in an initial "
						+ "transformula -- somewhat unexpected.. --> TODO: treat this case";
				validArrayTv = mMgdScript.constructFreshTermVariable(validArray.getGloballyUniqueId(),
						validArray.getSort());
				mMemlocInVars.put(validArray, validArrayTv);
				mMemlocOutVars.put(validArray, validArrayTv);
			}

//			final Map<IProgramNonOldVar, IProgramConst> memlocArrayToInitiLit = memlocArrayManager.getMemlocArrayToInitConstantArray();
			final Map<IProgramNonOldVar, Term> memlocArrayToInitiLit = memlocArrayManager.getMemlocArrayToInitConstantArray();

			// is this locking necessary? the script is used for creating Terms only
			mMgdScript.lock(this);

			final List<Term> initializingEquations = new ArrayList<>();
//			for (final Entry<IProgramNonOldVar, IProgramConst> en : freezeVarTofreezeVarLit.entrySet()) {
//			for (final Entry<IProgramNonOldVar, IProgramConst> en :
			for (final Entry<IProgramNonOldVar, Term> en : memlocArrayToInitiLit.entrySet()) {
				// variable for memloc array "memmloc_dim_sort"
				final TermVariable memlocArrayTv = mMgdScript.constructFreshTermVariable(en.getKey().getGloballyUniqueId(),
						en.getKey().getSort());

				// constant array (const-Array-sort1-sort2 memmloc_dim_sort_lit)
				final Term initConstArray = en.getValue();

				// "memloc_dim_sort = (const-Array-Int-Sort memloc_dim_sort_lit)"
				initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), memlocArrayTv, initConstArray));
				mMemlocInVars.put(en.getKey(), memlocArrayTv);
				mMemlocOutVars.put(en.getKey(), memlocArrayTv);

//				/*
//				 *  "valid[lit_frz_l_x] = 1"
//				 */
//				// TODO have to get the valid Termvariable from the Transformula or make a new one!
//				final Term select = SmtUtils.select(mMgdScript.getScript(), validArrayTv, frzLit);
//				final Term one = SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE);
//
//				initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), select, one));
			}


			/*
			 * furthermore add disequalities between all freeze var literals
			 */
			final List<Term> freezeLitDisequalities = new ArrayList<>();

//			if (mSettings.isAssumeFreezeVarLitDisequalitiesAtInitEdges()) {
//				for (final Entry<IProgramConst, IProgramConst> en : CrossProducts.binarySelectiveCrossProduct(
//						new HashSet<>(memlocArrayManager.getMemlocArrayToInitConstantArray().values()), false, false)) {
////						new HashSet<>(freezeVarTofreezeVarLit.values()), false, false)) {
//					freezeLitDisequalities.add(
//							mMgdScript.getScript().term("not",
//									mMgdScript.term(this, "=", en.getKey().getTerm(), en.getValue().getTerm())));
//				}
//			}

			mInitializingTerm = SmtUtils.and(mMgdScript.getScript(),
					SmtUtils.and(mMgdScript.getScript(), initializingEquations),
					SmtUtils.and(mMgdScript.getScript(), freezeLitDisequalities));

			mMgdScript.unlock(this);

		}

		public Term getInitializingTerm() {
			return mInitializingTerm;
		}

		public Map<IProgramVar, TermVariable> getFreezeVarInVars() {
			return mMemlocInVars;
		}

		public Map<IProgramVar, TermVariable> getFreezeVarOutVars() {
			return mMemlocOutVars;
		}
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "memlocinitializer";
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mNewSymbolTable;
	}
}
