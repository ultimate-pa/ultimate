/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirParser plug-in.
 *
 * The ULTIMATE LlvmirParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class UltimateLlvmirParser implements ISource {

	@Override
	public String getPluginID() {
		return getClass().getPackage().getName();
	}

	@Override
	public void init() {
		// Initialization logic if needed
	}

	@Override
	public String getPluginName() {
		return "LLVM IR Parser";
	}

	@Override
	public File[] parseable(final File[] files) {
		return Arrays.stream(files)
				.filter(file -> file.getName().endsWith(".ll") || file.getName().endsWith(".bc"))
				.toArray(File[]::new);
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		// Implement parsing logic here
		return null; // Placeholder return value
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".ll", ".bc" };
	}

	@Override
	public ModelType getOutputDefinition() {
		return ModelType.LLVM_IR; // Placeholder for actual model type definition
	}
}
