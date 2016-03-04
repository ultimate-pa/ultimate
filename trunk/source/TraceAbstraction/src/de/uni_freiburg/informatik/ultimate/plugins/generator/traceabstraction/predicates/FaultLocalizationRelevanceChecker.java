package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;

/**
 * Checks the relevance of a <code>CodeBlock</code> with respect to a pre- and a
 * postcondition. The check is reduced to a Hoare triple check.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class FaultLocalizationRelevanceChecker {
	/**
	 * Statement relevance information for fault localization.
	 * 
	 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
	 */
	public enum ERelevanceStatus {
		Sat,
		InUnsatCore,
		NotInUnsatCore,
		unknown
	}
	
	/**
	 * Used by Fault Localization to compute the relevance of statements.
	 * 
	 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
	 */
	private class FaultLocalizationHoareTripleChecker
			extends IncrementalHoareTripleChecker {
		private Annotation mAnnot = null;
		
		public FaultLocalizationHoareTripleChecker(SmtManager smtManager,
				ModifiableGlobalVariableManager modGlobVarManager) {
			super(smtManager, modGlobVarManager);
		}
		
		@Override
		protected boolean isAddAnnotation() {
			return true;
		}
		
		@Override
		protected void signalAnnotation(Annotation annot) {
			mAnnot = annot;
		}
	}
	
	private final FaultLocalizationHoareTripleChecker mHoareTripleChecker;
	private final SmtManager mSmtManager;
	
	public FaultLocalizationRelevanceChecker(final SmtManager smtManager,
			final ModifiableGlobalVariableManager modGlobVarManager) {
		this.mHoareTripleChecker = new FaultLocalizationHoareTripleChecker(
				smtManager, modGlobVarManager);
		this.mSmtManager = smtManager;
	}
	
	public ERelevanceStatus relevanceInternal(final IPredicate pre,
			final CodeBlock cb, final IPredicate succ) {
		// TODO negate succ?
		final Validity val = mHoareTripleChecker.checkInternal(pre, cb, succ);
		
		return getResult(val, mHoareTripleChecker.mAnnot);
	}
	
	/**
	 * @param val validity status from Hoare triple check
	 * @param mAnnot
	 * @return relevance
	 */
	private ERelevanceStatus getResult(final Validity val,
			final Annotation mAnnot) {
		final ERelevanceStatus result;
		switch (val) {
			case INVALID: // satisfiable
				result = ERelevanceStatus.Sat;
				break;
				
			case VALID: // unsatisfiable, check unsat core
				Term[] unsatCore = mSmtManager.getScript().getUnsatCore();
				boolean found = false;
				for (Term term : unsatCore) {
					if (term.equals(mAnnot)) { // TODO can we use == here?
						found = true;
						break;
					}
				}
				result = found
						? ERelevanceStatus.InUnsatCore
						: ERelevanceStatus.NotInUnsatCore;
				break;
				
			case UNKNOWN:
				result = ERelevanceStatus.unknown;
				break;
				
			case NOT_CHECKED:
			default:
				throw new IllegalArgumentException(String.format(
						"Hoare triple check returned status '%s'.", val));
		}
		return result;
	}
}