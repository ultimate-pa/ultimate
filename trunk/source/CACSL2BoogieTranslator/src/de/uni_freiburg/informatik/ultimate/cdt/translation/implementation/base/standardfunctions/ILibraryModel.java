package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.Collection;

import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public interface ILibraryModel {
	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	@FunctionalInterface
	interface IFunctionModelHandler {
		Result handleFunction(final IDispatcher main, final IASTFunctionCallExpression node, final ILocation loc,
				String methodName);
	}

	@FunctionalInterface
	interface ITypeModelHandler {
		TypesResult handleTypedefinition(IASTNamedTypeSpecifier node, ILocation loc);
	}

	public record FunctionModel(String functionName, IFunctionModelHandler model) {
		// empty
	}

	public record TypeModel(String typeName, ITypeModelHandler model) {
		// empty
	}

	Collection<FunctionModel> getFunctionModels();

	Collection<String> getUnsupportedFunctions();

	Collection<TypeModel> getTypeModels();
}
