/*
 * Copyright (C) 2025 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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

import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * An interface to abstract the model of libraries (mostly libraries from the C standard) in Boogie.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public interface ILibraryModel {
	/**
	 * An interface to represent the model of a library function.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	interface IFunctionModelHandler {
		/**
		 * Translates a library function.
		 *
		 * @param main
		 *            A dispatcher.
		 * @param node
		 *            A node for the function call.
		 * @param loc
		 *            A location.
		 * @param methodName
		 *            The name of the called function.
		 * @return The model of the call to a library function.
		 */
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}

	/**
	 * An interface to represent the model of a constant macro.
	 *
	 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	interface IConstantModelHandler {
		/**
		 * Models the constant as an {@link ExpressionResult}.
		 *
		 * @param loc
		 *            A location.
		 * @return An {@link ExpressionResult} as a model of the constant.
		 */
		ExpressionResult handleConstant(ILocation loc);
	}

	/**
	 * Model of a translated function, consisting of the name of the function and our translated model (represented as a
	 * {@link IFunctionModelHandler}).
	 */
	public record FunctionModel(String functionName, IFunctionModelHandler functionModel) {
		// empty
	}

	/**
	 * Model of a predefined type, consisting of the name of the type and our translated model (as a {@code ICType}).
	 */
	public record TypeModel(String typeName, ICType cType) {
		// empty
	}

	/**
	 * Model of a predefined constant, consisting of the name of the type and our translated model (represented as a
	 * {@link IConstantModelHandler}).
	 */
	public record ConstantModel(String name, IConstantModelHandler model) {
		// empty
	}

	/**
	 * Gets the model of the supported functions.
	 *
	 * @return a collection of {@link FunctionModel} of the functions that can be handled.
	 */
	default Collection<FunctionModel> getFunctionModels() {
		return List.of();
	}

	/**
	 * Gets the functions that are not supported.
	 *
	 * @return names of the unsupported functions, i.e., where we expect to cancel the translation on encounter.
	 */
	default Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

	/**
	 * Gets the model of the predefined types.
	 *
	 * @return a collection of {@link TypeModel} of the types that are defined.
	 */
	default Collection<TypeModel> getTypeModels() {
		return List.of();
	}

	/**
	 * Get the model of the predefined constants
	 *
	 * @return a collection of {@link ConstantModel} of the constants that are defined.
	 */
	default Collection<ConstantModel> getConstantModels() {
		return List.of();
	}
}
