/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTParser plug-in.
 *
 * The ULTIMATE CDTParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.settings.model.CExternalSetting;
import org.eclipse.cdt.core.settings.model.ICConfigurationDescription;
import org.eclipse.cdt.core.settings.model.ICSettingEntry;
import org.eclipse.cdt.core.settings.model.extension.CExternalSettingProvider;
import org.eclipse.cdt.core.settings.model.util.CDataUtil;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;

import de.uni_freiburg.informatik.ultimate.cdt.parser.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UltimateCdtExternalSettingsProvider extends CExternalSettingProvider {

	/** The ID of this ExternalSettingProvider as specified in the plugin XML */
	public static final String ID = "ultimateSettingsProviderId";

	@Override
	public CExternalSetting[] getSettings(final IProject project, final ICConfigurationDescription cfg) {
		final ToolchainDependency td;
		try {
			td = ToolchainDependency.extract(project);
		} catch (final CoreException e) {
			throw new RuntimeException(e);
		}
		final List<ICSettingEntry> includeSettings = new ArrayList<>();
		final String includes =
				td.mServices.getPreferenceProvider(Activator.PLUGIN_ID).getString(PreferenceInitializer.INCLUDE_PATHS);
		for (final String includePath : includes.split(";")) {
			if (!new File(includePath).exists()) {
				continue;
			}
			td.mLogger.info("Adding includes from " + includePath);
			final File[] includeFiles = new File(includePath).listFiles();
			Arrays.stream(includeFiles)
					.map(a -> CDataUtil.createCIncludeFileEntry(a.getAbsolutePath(), ICSettingEntry.BUILTIN))
					.forEach(includeSettings::add);
			includeSettings.add(CDataUtil.createCIncludePathEntry(includePath, ICSettingEntry.BUILTIN));
		}

		final ICSettingEntry[] settings = includeSettings.toArray(new ICSettingEntry[includeSettings.size()]);
		return new CExternalSetting[] { new CExternalSetting(null, null, null, settings) };
	}

	public final static class ToolchainDependency {

		private final IUltimateServiceProvider mServices;
		private final ILogger mLogger;

		public ToolchainDependency(final IUltimateServiceProvider services, final ILogger logger) {
			mServices = services;
			mLogger = logger;
		}

		public static void annotate(final IProject project, final IUltimateServiceProvider services,
				final ILogger logger) throws CoreException {
			final ToolchainDependency dependency = new ToolchainDependency(services, logger);
			final QualifiedName qname = new QualifiedName(ToolchainDependency.class.getName(), project.getName());
			project.setSessionProperty(qname, dependency);
		}

		public static ToolchainDependency extract(final IProject project) throws CoreException {
			final QualifiedName qname = new QualifiedName(ToolchainDependency.class.getName(), project.getName());
			final Object property = project.getSessionProperty(qname);
			project.setSessionProperty(qname, null);
			return (ToolchainDependency) property;
		}
	}

}
