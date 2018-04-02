package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

class ComputeMemlocInitializingTransformula {

		private final ManagedScript mMgdScript;
		// result fields
		private Term mInitializingTerm;
		private Map<IProgramVar, TermVariable> mMemlocInVars;
		private Map<IProgramVar, TermVariable> mMemlocOutVars;

		private final HeapSepSettings mSettings;

		private final MemlocArrayManager mMemlocArrayManager;
		private final UnmodifiableTransFormula mResult;

		ComputeMemlocInitializingTransformula(final MemlocArrayManager memlocArrayManager,
				final IProgramVar validArray, //final UnmodifiableTransFormula originalTransFormula,
				final HeapSepSettings settings, final ManagedScript mgdScript) {
			mMgdScript = mgdScript;
			mSettings = Objects.requireNonNull(settings);
			mMemlocArrayManager = memlocArrayManager;
			computeInitializingTerm(Objects.requireNonNull(memlocArrayManager),
					Objects.requireNonNull(validArray));
//					Objects.requireNonNull(originalTransFormula));
			mResult = computeInitializingTransformula();
		}

		private void computeInitializingTerm(final MemlocArrayManager memlocArrayManager,
				final IProgramVar validArray) {
			mMemlocInVars = new HashMap<>();
			mMemlocOutVars = new HashMap<>();

			final Map<IProgramNonOldVar, Term> memlocArrayToInitiLit =
					memlocArrayManager.getMemlocArrayToInitConstantArray();

			// is this locking necessary? the script is used for creating Terms only
			mMgdScript.lock(this);

			final List<Term> initializingEquations = new ArrayList<>();
			for (final Entry<IProgramNonOldVar, Term> en : memlocArrayToInitiLit.entrySet()) {

				// variable for memloc array "memmloc_dim_sort"
				final TermVariable memlocArrayTv;
//				boolean memlocUpdateInTf;
//				if (originalTransFormula.getInVars().containsKey(en.getKey())) {
//					// invar already present (i.e. there already is an memloc update in this transformula)
//					memlocUpdateInTf = true;
//					memlocArrayTv = originalTransFormula.getInVars().get(en.getKey());
//				} else {
//					memlocUpdateInTf = false;
					memlocArrayTv = mMgdScript.constructFreshTermVariable(en.getKey().getGloballyUniqueId(),
							en.getKey().getSort());
//				}

				// constant array (const-Array-sort1-sort2 memmloc_dim_sort_lit)
				final Term initConstArray = en.getValue();

				// "memloc_dim_sort = (const-Array-Int-Sort memloc_dim_sort_lit)" (assume statement so to say)
				initializingEquations.add(SmtUtils.binaryEquality(mMgdScript.getScript(), memlocArrayTv, initConstArray));

//				if (!memlocUpdateInTf) {
					mMemlocInVars.put(en.getKey(), memlocArrayTv);
					mMemlocOutVars.put(en.getKey(), memlocArrayTv);
//				}
			}

			/*
			 * furthermore add disequalities between all freeze var literals
			 */
			final List<Term> freezeLitDisequalities = new ArrayList<>();

			mInitializingTerm = SmtUtils.and(mMgdScript.getScript(),
					SmtUtils.and(mMgdScript.getScript(), initializingEquations),
					SmtUtils.and(mMgdScript.getScript(), freezeLitDisequalities));

			mMgdScript.unlock(this);

		}

		Map<IProgramVar, TermVariable> getMemlocInVars() {
			return mMemlocInVars;
		}

		Map<IProgramVar, TermVariable> getMemlocOutVars() {
			return mMemlocOutVars;
		}

		public UnmodifiableTransFormula computeInitializingTransformula() {
			/*
			 *  steps:
			 *  <li> add a conjunct with equalities l_x_frz = lit_l_x_frz (l means a location) to the Transformula's
			 *    formula
			 *  <li> add all l_x_frz as assigned vars to the invars/outvars
			 */

//			final ComputeInitializingTerm cit =
//					new ComputeInitializingTerm(mMemlocArrayManager, mValidArray, oldTransformula, mSettings);

			final Map<IProgramVar, TermVariable> newInVars = getMemlocInVars();
//			final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(oldTransformula.getInVars());
//			newInVars.putAll(cit.getMemlocInVars());
//			for (final IProgramVar iv : cit.getMemlocInVars().keySet()) {
//				if (iv instanceof IProgramOldVar) {
//					continue;
//				}
//				mNewSymbolTable.add(iv);
//			}

			final Map<IProgramVar, TermVariable> newOutVars = getMemlocOutVars();
//			final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>(oldTransformula.getOutVars());
//			newOutVars.putAll(cit.getMemlocOutVars());
//			for (final IProgramVar iv : cit.getMemlocOutVars().keySet()) {
//				if (iv instanceof IProgramOldVar) {
//					continue;
//				}
//				mNewSymbolTable.add(iv);
//			}

			/*
			 * Note that the symbol table will be automatically updated with the new constants by the
			 *  TransformedIcfgBuilder (in its .finish() method).
			 */
			final Set<IProgramConst> newNonTheoryConstants = new HashSet<>(mMemlocArrayManager.getMemLocLits());
//			final Set<IProgramConst> newNonTheoryConstants = DataStructureUtils.union(
//					oldTransformula.getNonTheoryConsts(),
//					new HashSet<>(mMemlocArrayManager.getMemLocLits()));
//			for (final IProgramConst lit : mMemlocArrayManager.getMemLocLits()) {
//				mNewSymbolTable.add(lit);
//			}

			final TransFormulaBuilder newTfBuilder = new TransFormulaBuilder(
					newInVars, newOutVars, newNonTheoryConstants.isEmpty(), newNonTheoryConstants,
					true, null, true);

			/*
			 * conjoin the original transformula with the initializing term
			 */
			final Term newFormula = mInitializingTerm;

			newTfBuilder.setFormula(newFormula);
			newTfBuilder.setInfeasibility(Infeasibility.UNPROVEABLE);
//			newTfBuilder.addAuxVarsButRenameToFreshCopies(oldTransformula.getAuxVars(), mMgdScript);

			final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);

			return newTransformula;
		}

		public UnmodifiableTransFormula getResult() {
			return mResult;
		}
	}