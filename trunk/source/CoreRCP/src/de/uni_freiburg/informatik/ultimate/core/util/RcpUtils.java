/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CLI plug-in.
 *
 * The ULTIMATE CLI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CLI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CLI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CLI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CLI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.util;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.Dictionary;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.URIUtil;
import org.eclipse.osgi.service.datalocation.Location;
import org.eclipse.osgi.service.environment.EnvironmentInfo;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;
import org.osgi.framework.ServiceReference;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions.UncheckedURISyntaxException;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil.UrlConverter;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RcpUtils {
	private RcpUtils() {
		// utility class
	}

	public static String getVersion(final String pluginId) {
		final Bundle bundle = Platform.getBundle(pluginId);
		if (bundle == null) {
			return "UNKNOWN";
		}
		final Dictionary<String, String> headers = bundle.getHeaders();
		if (headers != null) {
			return headers.get("Bundle-Version");
		}
		return "UNKNOWN";
	}

	public static File getWorkingDirectory() {
		try {
			return URIUtil.toFile(Platform.getInstallLocation().getURL().toURI());
		} catch (final URISyntaxException e) {
			throw new UncheckedURISyntaxException(e);
		}
	}

	public static String getInstanceLocationPath() {
		final Location instloc = Platform.getInstanceLocation();
		if (instloc != null) {
			final URL url = instloc.getURL();
			if (url != null) {
				return url.getPath();
			}
		}
		return null;
	}

	public static String[] getFrameworkArguments() {
		final EnvironmentInfo envInfo = getEnvironmentInfo();
		return envInfo.getFrameworkArgs();
	}

	public static EnvironmentInfo getEnvironmentInfo() {
		final BundleContext bc = Platform.getBundle(Activator.PLUGIN_ID).getBundleContext();
		if (bc == null) {
			return null;
		}
		final ServiceReference<EnvironmentInfo> infoRef =
				(ServiceReference<EnvironmentInfo>) bc.getServiceReference(EnvironmentInfo.class.getName());
		if (infoRef == null) {
			return null;
		}
		final EnvironmentInfo envInfo = bc.getService(infoRef);
		if (envInfo == null) {
			return null;
		}
		bc.ungetService(infoRef);
		return envInfo;
	}

	/**
	 * Create an UrlConverter instance that can be retrieved using reflection to avoid explicit dependencies in
	 * {@link ReflectionUtil}.
	 */
	public static UrlConverter getBundleProtocolResolver() {
		return url -> FileLocator.toFileURL(url);
	}
}
