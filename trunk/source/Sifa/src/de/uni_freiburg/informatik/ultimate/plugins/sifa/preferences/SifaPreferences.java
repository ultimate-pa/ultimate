/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Sifa plug-in.
 *
 * The ULTIMATE Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.sifa.preferences;

import java.util.Arrays;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.AlwaysFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.LogSizeWrapperFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.NeverFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.SizeLimitFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.FixpointLoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.InterpretCallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ReUseSupersetCallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.TopInputCallSummarizer;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.sifa.SifaBuilder;

/**
 * Description, values, and default values for sifa settings.
 * Use {@link SifaBuilder} to create a sifa interpreter using these settings.
 * <p>
 * When adding settings to this class you also have to adapt the methods in {@link SifaBuilder}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SifaPreferences extends UltimatePreferenceInitializer {

	public static final String LABEL_ABSTRACT_DOMAIN = "Abstract Domain";
	private static final String DEFAULT_ABSTRACT_DOMAIN = CompoundDomain.class.getSimpleName();
	private static final String[] VALUES_ABSTRACT_DOMAIN = {
		ExplicitValueDomain.class.getSimpleName(),
		IntervalDomain.class.getSimpleName(),
		CompoundDomain.class.getSimpleName(),
	};

	public static final String LABEL_LOOP_SUMMARIZER = "Loop Summarizer";
	private static final String DEFAULT_LOOP_SUMMARIZER = FixpointLoopSummarizer.class.getSimpleName();
	private static final String[] VALUES_LOOP_SUMMARIZER = {
		FixpointLoopSummarizer.class.getSimpleName(),
	};

	public static final String LABEL_CALL_SUMMARIZER = "Call Summarizer";
	private static final String DEFAULT_CALL_SUMMARIZER = ReUseSupersetCallSummarizer.class.getSimpleName();
	private static final String[] VALUES_CALL_SUMMARIZER = {
		TopInputCallSummarizer.class.getSimpleName(),
		InterpretCallSummarizer.class.getSimpleName(),
		ReUseSupersetCallSummarizer.class.getSimpleName(),
	};

	public static final String LABEL_FLUID = "Fluid";
	private static final String TOOLTIP_FLUID = "Decides when to apply abstraction";
	private static final String DEFAULT_FLUID = SizeLimitFluid.class.getSimpleName();
	private static final String[] VALUES_FLUID = {
		NeverFluid.class.getSimpleName(),
		SizeLimitFluid.class.getSimpleName(),
		AlwaysFluid.class.getSimpleName(),
		LogSizeWrapperFluid.class.getSimpleName(),
	};

	public static final String LABEL_SIMPLIFICATION = "Simplification Technique";
	private static final SimplificationTechnique DEFAULT_SIMPLIFICATION = SimplificationTechnique.NONE;
	private static final SimplificationTechnique[] VALUES_SIMPLIFICATION = SimplificationTechnique.values();
	public static final Class<SimplificationTechnique> CLASS_SIMPLIFICATION = SimplificationTechnique.class;

	public static final String LABEL_XNF_CONVERSION = "Xnf Conversion Technique";
	private static final XnfConversionTechnique DEFAULT_XNF_CONVERSION =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	private static final XnfConversionTechnique[] VALUES_XNF_CONVERSION = XnfConversionTechnique.values();
	public static final Class<XnfConversionTechnique> CLASS_XNF_CONVERSION = XnfConversionTechnique.class;

	// ---- settings in containers ----

	// settings specific to ExplicitValueDomain
	public static final String LABEL_EXPLVALDOM_MAX_PARALLEL_STATES = "Max. Parallel Explicit Values";
	private static final int DEFAULT_EXPLVALDOM_MAX_PARALLEL_STATES = 2;

	// settings specific to IntervalDomain
	public static final String LABEL_INTERVALDOM_MAX_PARALLEL_STATES = "Max. Parallel Intervals";
	private static final int DEFAULT_INTERVALDOM_MAX_PARALLEL_STATES = 2;

	// settings specific to CompoundDomain
	public static final String LABEL_COMPOUNDDOM_SUBDOM = "Intern domains";
	private static final String DEFAULT_COMPOUNDDOM_SUBDOM =
			ExplicitValueDomain.class.getSimpleName() + ";" + IntervalDomain.class.getSimpleName();
	private static final String[] CHOICES_COMPOUNDDOM_SUBDOM = filter(VALUES_ABSTRACT_DOMAIN,
			value -> !CompoundDomain.class.getSimpleName().equals(value));
	private static final String TOOLTIP_COMPOUNDDOM_SUBDOM = "List subdomains separated by `;`. Valid subdomains are\n"
			+ String.join("\n", CHOICES_COMPOUNDDOM_SUBDOM);
	public static class SubdomainValidator implements IUltimatePreferenceItemValidator<String> {
		public static Stream<String> subdomains(final String setting) {
			return Arrays.stream(setting.split(";"));
		}
		@Override
		public boolean isValid(final String setting) {
			return subdomains(setting).allMatch(SubdomainValidator::isValidSubDom);
		}
		private static boolean isValidSubDom(final String token) {
			return Arrays.stream(CHOICES_COMPOUNDDOM_SUBDOM).anyMatch(validChoice -> validChoice.equals(token));
		}
		@Override
		public String getInvalidValueErrorMessage(final String setting) {
			return subdomains(setting)
					.filter(subdom -> !isValidSubDom(subdom))
					.map(subdom -> String.format("Not a valid subdomain: %s", subdom))
					.collect(Collectors.joining("\n"));
		}
	}

	// settings specific to LogSizeWrapperFluid
	public static final String LABEL_LOGFLUID_INTERN_FLUID = "Intern Fluid";
	private static final String DEFAULT_LOGFLUID_INTERN_FLUID = DEFAULT_FLUID;
	private static final String[] VALUES_LOGFLUID_INTERN_FLUID_VALUES = filter(VALUES_FLUID,
			value -> !LogSizeWrapperFluid.class.getSimpleName().equals(value));

	// settings specific to SizeLimitFluid
	public static final String LABEL_SIZELIMITFLUID_MAX_DAGSIZE= "Abstract when formula's dag size exceeds\n"
			+ "(negative numbers disable this limit)";
	private static final int DEFAULT_SIZELIMITFLUID_MAX_DAGSIZE = -1;

	public static final String LABEL_SIZELIMITFLUID_MAX_DISJUNCTS= "Abstract when formula has more disjuncts than\n"
			+ "(negative numbers disable this limit)";
	private static final int DEFAULT_SIZELIMITFLUID_MAX_DISJUNCTS = 8;




	// ↑ Members ----- ↓ Methods ---------------------------------------------



	public SifaPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {

		final UltimatePreferenceItemContainer containerExplValDom =
				new UltimatePreferenceItemContainer(ExplicitValueDomain.class.getSimpleName());
		containerExplValDom.addItem(integer(LABEL_EXPLVALDOM_MAX_PARALLEL_STATES,
				DEFAULT_EXPLVALDOM_MAX_PARALLEL_STATES, 1, Integer.MAX_VALUE));

		final UltimatePreferenceItemContainer containerIntervalDom =
				new UltimatePreferenceItemContainer(IntervalDomain.class.getSimpleName());
		containerIntervalDom.addItem(integer(LABEL_INTERVALDOM_MAX_PARALLEL_STATES,
				DEFAULT_INTERVALDOM_MAX_PARALLEL_STATES, 1, Integer.MAX_VALUE));

		final UltimatePreferenceItemContainer containerCompoundDom =
				new UltimatePreferenceItemContainer(CompoundDomain.class.getSimpleName());
		containerCompoundDom.addItem(string(LABEL_COMPOUNDDOM_SUBDOM, TOOLTIP_COMPOUNDDOM_SUBDOM,
				DEFAULT_COMPOUNDDOM_SUBDOM, new SubdomainValidator()));

		final UltimatePreferenceItemContainer containerLogFluid =
				new UltimatePreferenceItemContainer(LogSizeWrapperFluid.class.getSimpleName());
		containerLogFluid.addItem(combo(LABEL_LOGFLUID_INTERN_FLUID,
				DEFAULT_LOGFLUID_INTERN_FLUID, VALUES_LOGFLUID_INTERN_FLUID_VALUES));

		final UltimatePreferenceItemContainer containerSizeLimitFluid =
				new UltimatePreferenceItemContainer(SizeLimitFluid.class.getSimpleName());
		containerSizeLimitFluid.addItem(integer(LABEL_SIZELIMITFLUID_MAX_DAGSIZE, DEFAULT_SIZELIMITFLUID_MAX_DAGSIZE));
		containerSizeLimitFluid.addItem(integer(LABEL_SIZELIMITFLUID_MAX_DISJUNCTS, DEFAULT_SIZELIMITFLUID_MAX_DISJUNCTS));

		return new BaseUltimatePreferenceItem[] {
			combo(LABEL_ABSTRACT_DOMAIN, DEFAULT_ABSTRACT_DOMAIN, VALUES_ABSTRACT_DOMAIN),
			combo(LABEL_LOOP_SUMMARIZER, DEFAULT_LOOP_SUMMARIZER, VALUES_LOOP_SUMMARIZER),
			combo(LABEL_CALL_SUMMARIZER, DEFAULT_CALL_SUMMARIZER, VALUES_CALL_SUMMARIZER),
			combo(LABEL_FLUID, TOOLTIP_FLUID, DEFAULT_FLUID, VALUES_FLUID),
			//
			combo(LABEL_SIMPLIFICATION, DEFAULT_SIMPLIFICATION, VALUES_SIMPLIFICATION),
			combo(LABEL_XNF_CONVERSION, DEFAULT_XNF_CONVERSION, VALUES_XNF_CONVERSION),
			//
			containerExplValDom,
			containerIntervalDom,
			containerCompoundDom,
			containerLogFluid,
			containerSizeLimitFluid,
		};
	}

	public static IPreferenceProvider getPreferenceProvider(final IUltimateServiceProvider services) {
		return services.getPreferenceProvider(Activator.PLUGIN_ID);
	}

	private static <T> UltimatePreferenceItem<T> combo(final String label, final T defaultValue, final T[] values) {
		return new UltimatePreferenceItem<>(label, defaultValue, PreferenceType.Combo, values);
	}

	private static <T> UltimatePreferenceItem<T> combo(final String label, final String tooltip,
			final T defaultValue, final T[] values) {
		return new UltimatePreferenceItem<>(
				label, defaultValue, PreferenceType.Combo, tooltip, false, values, null);
	}

	private static UltimatePreferenceItem<Integer> integer(final String label, final int defaultValue) {
		return integer(label, defaultValue, Integer.MIN_VALUE, Integer.MAX_VALUE);
	}

	private static UltimatePreferenceItem<Integer> integer(final String label, final int defaultValue,
			final int min, final int max) {
		return new UltimatePreferenceItem<>(label, defaultValue,
				PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(min, max));
	}

	private static UltimatePreferenceItem<String> string(
			final String label, final String tooltip, final String defaultValue,
			final IUltimatePreferenceItemValidator<String> validator) {
		return new UltimatePreferenceItem<>(label, defaultValue, tooltip, PreferenceType.String, validator);
	}

	private static UltimatePreferenceItem<Boolean> bool(
			final String label, final String tooltip, final boolean defaultValue) {
		return new UltimatePreferenceItem<>(label, defaultValue, tooltip, PreferenceType.Boolean);
	}

	private static String[] filter(final String[] array, final Predicate<String> keep) {
		return Arrays.stream(array).filter(keep).toArray(String[]::new);
	}
}
