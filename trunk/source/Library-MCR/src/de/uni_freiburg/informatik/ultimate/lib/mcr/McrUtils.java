package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class McrUtils {
	private McrUtils() {
	}

	public static Set<TermVariable> getTermVariables(final Collection<IProgramVar> vars) {
		return vars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public static Term abstractVariables(final Term term, final Set<TermVariable> varsToKeep, final int quantifier,
			final ManagedScript managedScript, final IUltimateServiceProvider services) {
		final Term withoutIte = new IteRemover(managedScript).transform(term);
		final Term nnf = new NnfTransformer(managedScript, services, QuantifierHandling.KEEP).transform(withoutIte);
		final List<TermVariable> quantifiedVars =
				Arrays.stream(nnf.getFreeVars()).filter(x -> !varsToKeep.contains(x)).collect(Collectors.toList());
		final Term quantified = SmtUtils.quantifier(managedScript.getScript(), quantifier, quantifiedVars, nnf);
		// TODO: What to use as PqeTechnique?
		return new QuantifierPusher(managedScript, services, false, PqeTechniques.ONLY_DER).transform(quantified);
	}

	public static Term replaceQuantifiers(final Term term, final Term replacement) {
		return new SubstituteQuantifiers(replacement).transform(term);
	}

	static class SubstituteQuantifiers extends TermTransformer {
		private final Term mReplacement;

		SubstituteQuantifiers(final Term replacement) {
			mReplacement = replacement;
		}

		@Override
		protected void convert(final Term term) {
			if (term instanceof QuantifiedFormula) {
				setResult(mReplacement);
			} else {
				super.convert(term);
			}
		}
	}
}
