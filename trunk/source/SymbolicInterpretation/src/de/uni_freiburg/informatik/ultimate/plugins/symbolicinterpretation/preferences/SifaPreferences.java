/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE SymbolicInterpretation plug-in.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation.preferences;

import java.util.Arrays;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.lib.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.BaseUltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem.IUltimatePreferenceItemValidator;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemContainer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.AlwaysFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.LogSizeWrapperFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.fluid.NeverFluid;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.FixpointLoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.summarizers.TopInputCallSummarizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.symbolicinterpretation.SifaBuilder;

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
	public static final String DEFAULT_ABSTRACT_DOMAIN = ExplicitValueDomain.class.getSimpleName();
	protected static final String[] VALUES_ABSTRACT_DOMAIN = {
		ExplicitValueDomain.class.getSimpleName(),
		IntervalDomain.class.getSimpleName(),
	};

	public static final String LABEL_LOOP_SUMMARIZER = "Loop Summarizer";
	public static final String DEFAULT_LOOP_SUMMARIZER = FixpointLoopSummarizer.class.getSimpleName();
	protected static final String[] VALUES_LOOP_SUMMARIZER = {
		FixpointLoopSummarizer.class.getSimpleName(),
	};

	public static final String LABEL_CALL_SUMMARIZER = "Call Summarizer";
	public static final String DEFAULT_CALL_SUMMARIZER = TopInputCallSummarizer.class.getSimpleName();
	protected static final String[] VALUES_CALL_SUMMARIZER = {
		TopInputCallSummarizer.class.getSimpleName(),
	};

	public static final String LABEL_FLUID = "Fluid";
	public static final String TOOLTIP_FLUID = "Decides when to apply abstraction";
	public static final String DEFAULT_FLUID = NeverFluid.class.getSimpleName();
	protected static final String[] VALUES_FLUID = {
		NeverFluid.class.getSimpleName(),
		AlwaysFluid.class.getSimpleName(),
		LogSizeWrapperFluid.class.getSimpleName(),
	};

	public static final String LABEL_SIMPLIFICATION = "Simplification Technique";
	public static final SimplificationTechnique DEFAULT_SIMPLIFICATION = SimplificationTechnique.SIMPLIFY_DDA;
	protected static final SimplificationTechnique[] VALUES_SIMPLIFICATION = SimplificationTechnique.values();
	public static final Class<SimplificationTechnique> CLASS_SIMPLIFICATION = SimplificationTechnique.class;

	public static final String LABEL_XNF_CONVERSION = "Xnf Conversion Technique";
	public static final XnfConversionTechnique DEFAULT_XNF_CONVERSION =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	protected static final XnfConversionTechnique[] VALUES_XNF_CONVERSION = XnfConversionTechnique.values();
	public static final Class<XnfConversionTechnique> CLASS_XNF_CONVERSION = XnfConversionTechnique.class;

	// ---- settings in containers ----

	// settings specific to ExplicitValueDomain
	public static final String LABEL_EXPLVALDOM_PARALLEL_STATES = "Parallel States";
	public static final int DEFAULT_EXPLVALDOM_PARALLEL_STATES = 2;

	// settings specific to LoggerFluid
	public static final String LABEL_LOGFLUID_INTERN_FLUID = "Intern Fluid";
	public static final String DEFAULT_LOGFLUID_INTERN_FLUID = NeverFluid.class.getSimpleName();
	protected static final String[] VALUES_LOGFLUID_INTERN_FLUID_VALUES = filter(VALUES_FLUID,
			value -> !LogSizeWrapperFluid.class.getSimpleName().equals(value));

	public SifaPreferences() {
		super(Activator.PLUGIN_ID, Activator.PLUGIN_NAME);
	}

	@Override
	protected BaseUltimatePreferenceItem[] initDefaultPreferences() {

		final UltimatePreferenceItemContainer containerExplValDom =
				new UltimatePreferenceItemContainer(ExplicitValueDomain.class.getSimpleName());
		containerExplValDom.addItem(integer(LABEL_EXPLVALDOM_PARALLEL_STATES,
				DEFAULT_EXPLVALDOM_PARALLEL_STATES, 1, Integer.MAX_VALUE));

		final UltimatePreferenceItemContainer containerLogFluid =
				new UltimatePreferenceItemContainer(LogSizeWrapperFluid.class.getSimpleName());
		containerLogFluid.addItem(combo(LABEL_LOGFLUID_INTERN_FLUID,
				DEFAULT_LOGFLUID_INTERN_FLUID, VALUES_LOGFLUID_INTERN_FLUID_VALUES));

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
			containerLogFluid,
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

	private static UltimatePreferenceItem<Integer> integer(final String label, final int defaultValue,
			final int min, final int max) {
		return new UltimatePreferenceItem<>(label, defaultValue,
				PreferenceType.Integer, new IUltimatePreferenceItemValidator.IntegerValidator(min, max));
	}

	private static String[] filter(final String[] array, final Predicate<String> keep) {
		return Arrays.stream(array).filter(keep).toArray(String[]::new);
	}
}
