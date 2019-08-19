package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
			mResult = computeInitializingTransformula();
		}

		private void computeInitializingTerm(final MemlocArrayManager memlocArrayManager,
				final IProgramVar validArray) {
			mMemlocInVars = new HashMap<>();
			mMemlocOutVars = new HashMap<>();

			final Set<IProgramNonOldVar> globalLocArrays = memlocArrayManager.getGlobalLocArrays();

			// is this locking necessary? the script is used for creating Terms only
			mMgdScript.lock(this);

			final List<Term> initializingEquations = new ArrayList<>();
			for (final IProgramNonOldVar locArray : globalLocArrays) {

				// variable for memloc array "memmloc_dim_sort"
				final TermVariable memlocArrayTv = mMgdScript.constructFreshTermVariable(locArray.getGloballyUniqueId(),
							locArray.getSort());

				// constant array (const-Array-sort1-sort2 memmloc_dim_sort_lit)
				final Term initConstArray = mMemlocArrayManager.getInitConstArrayForGlobalLocArray(locArray, this);

				// "memloc_dim_sort = (const-Array-Int-Sort memloc_dim_sort_lit)" (assume statement so to say)
				initializingEquations.add(
						SmtUtils.binaryEquality(mMgdScript.getScript(), memlocArrayTv, initConstArray));

				mMemlocInVars.put(locArray, memlocArrayTv);
				mMemlocOutVars.put(locArray, memlocArrayTv);
			}

			/*
			 * furthermore add disequalities between all freeze var literals
			 */
			mInitializingTerm = SmtUtils.and(mMgdScript.getScript(), initializingEquations);

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


			final Map<IProgramVar, TermVariable> newInVars = getMemlocInVars();

			final Map<IProgramVar, TermVariable> newOutVars = getMemlocOutVars();

			/*
			 * Note that the symbol table will be automatically updated with the new constants by the
			 *  TransformedIcfgBuilder (in its .finish() method).
			 */
			final Set<IProgramConst> newNonTheoryConstants = new HashSet<>(mMemlocArrayManager.getInitLocLits());

			final TransFormulaBuilder newTfBuilder = new TransFormulaBuilder(
					newInVars, newOutVars, newNonTheoryConstants.isEmpty(), newNonTheoryConstants,
					true, null, true);

			/*
			 * conjoin the original transformula with the initializing term
			 */
			final Term newFormula = mInitializingTerm;

			newTfBuilder.setFormula(newFormula);
			newTfBuilder.setInfeasibility(Infeasibility.UNPROVEABLE);

			final UnmodifiableTransFormula newTransformula = newTfBuilder.finishConstruction(mMgdScript);

			return newTransformula;
		}

		public UnmodifiableTransFormula getResult() {
			return mResult;
		}
	}