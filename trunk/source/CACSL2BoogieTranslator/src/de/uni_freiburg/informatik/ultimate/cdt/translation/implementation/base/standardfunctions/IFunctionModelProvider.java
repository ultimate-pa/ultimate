package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions.StandardFunctionHandler.IFunctionModelHandler;

public interface IFunctionModelProvider {
	public record FunctionModel(String functionName, IFunctionModelHandler model) {
		// empty
	}

	Collection<FunctionModel> getFunctionModels();

	Collection<String> getUnsupportedFunctions();
}
