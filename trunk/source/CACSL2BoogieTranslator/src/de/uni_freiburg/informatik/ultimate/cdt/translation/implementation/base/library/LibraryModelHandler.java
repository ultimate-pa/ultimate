/*
 * Copyright (C) 2013-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2020 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021-2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.library;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * The {@link LibraryModelHandler} creates the translation for various functions and types where we have our own
 * specification or implementation. This is typically the case for functions defined in the C standard, but also for
 * various standard libraries or SV-COMP extensions.
 *
 * @author Markus Lindenmann,
 * @author Matthias Heizmann
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class LibraryModelHandler {
	private final LocationFactory mLocationFactory;
	private final Map<String, IFunctionModelHandler> mFunctionModels;
	private final Map<String, ICType> mTypeModels;
	private final Map<String, IASTNode> mFunctionTable;
	private final FlatSymbolTable mSymboltable;
	private final ILogger mLogger;

	public LibraryModelHandler(final ILogger logger, final Map<String, IASTNode> functionTable,
			final FlatSymbolTable symboltable, final LocationFactory locationFactory,
			final List<ILibraryModel> libraryModels) {
		mLogger = logger;
		mFunctionTable = functionTable;
		mSymboltable = symboltable;
		mLocationFactory = locationFactory;
		mFunctionModels = getFunctionModels(libraryModels);
		mTypeModels = getTypeModels(libraryModels);
	}

	/**
	 * Check if the given function has an "integrated" specification or implementation and return a {@link Result} that
	 * contains a translation of the function if this is the case.
	 *
	 * Return null otherwise.
	 *
	 * @param main
	 * @param node
	 * @return
	 */
	public Result translateStandardFunction(final IDispatcher main, final IASTFunctionCallExpression node) {
		if (!(node.getFunctionNameExpression() instanceof final IASTIdExpression id)) {
			return null;
		}
		final String name = id.getName().toString();

		final IFunctionModelHandler functionModel = mFunctionModels.get(name);
		if (functionModel != null) {
			final String transformedName = mSymboltable.applyMultiparseRenaming(node.getContainingFilename(), name);
			final IASTNode funDecl = mFunctionTable.get(transformedName);
			if (funDecl instanceof IASTFunctionDefinition) {
				// it is a function that already has a body
				mLogger.warn("Function %s is already implemented but we override the implementation for the call at %s",
						transformedName, node.getFileLocation());
			}
			final ILocation loc = mLocationFactory.createCLocation(node);
			return functionModel.handleFunction(main, node, loc, name);
		}
		return null;
	}

	public Map<String, ICType> getTypeModels() {
		return mTypeModels;
	}

	private static Map<String, IFunctionModelHandler> getFunctionModels(final List<ILibraryModel> libraryModels) {
		final IFunctionModelHandler die = (main, node, loc, name) -> {
			throw new UnsupportedSyntaxException(loc, "Unsupported function: " + name);
		};
		final Map<String, IFunctionModelHandler> map = new HashMap<>();
		for (final var model : libraryModels) {
			for (final var fun : model.getFunctionModels()) {
				fill(map, fun.functionName(), fun.functionModel());
			}
			for (final var unsupportedName : model.getUnsupportedFunctions()) {
				fill(map, unsupportedName, die);
			}
		}
		return Collections.unmodifiableMap(map);
	}

	private static Map<String, ICType> getTypeModels(final List<ILibraryModel> libraryModels) {
		final Map<String, ICType> map = new HashMap<>();
		for (final var model : libraryModels) {
			for (final var type : model.getTypeModels()) {
				fill(map, type.typeName(), type.cType());
			}
		}

		return Collections.unmodifiableMap(map);
	}

	private static <K, V> void fill(final Map<K, V> map, final K key, final V value) {
		final V old = map.put(key, value);
		if (old != null) {
			throw new AssertionError("Accidentally overwrote definition for " + key);
		}
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	interface IFunctionModelHandler {
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}
}
