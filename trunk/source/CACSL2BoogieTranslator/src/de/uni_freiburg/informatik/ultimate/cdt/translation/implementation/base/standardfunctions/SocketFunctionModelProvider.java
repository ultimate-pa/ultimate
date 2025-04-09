package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

public class SocketFunctionModelProvider extends FunctionModelProvider {
	public SocketFunctionModelProvider(final AuxVarInfoBuilder auxVarInfoBuilder, final INameHandler nameHandler,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final ProcedureManager procedureManager,
			final TypeSizes typeSizes, final TranslationSettings settings,
			final ExpressionResultTransformer expressionResultTransformer, final ITypeHandler typeHandler,
			final CExpressionTranslator cEpressionTranslator, final DataRaceChecker dataRaceChecker) {
		super(auxVarInfoBuilder, nameHandler, expressionTranslation, memoryHandler, typeSizeAndOffsetComputer,
				procedureManager, typeSizes, settings, expressionResultTransformer, typeHandler, cEpressionTranslator,
				dataRaceChecker);
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		/**
		 * Function from socket.h (see https://pubs.opengroup.org/onlinepubs/009604499/basedefs/sys/socket.h.html). We
		 * simply overapproximate the return values of these functions
		 */
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/accept.html
		result.add(new FunctionModel("accept", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/bind.html
		result.add(new FunctionModel("bind", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/connect.html
		result.add(new FunctionModel("connect", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/listen.html
		result.add(new FunctionModel("listen", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 2, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/socket.html
		result.add(new FunctionModel("socket", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/recv.html
		result.add(new FunctionModel("recv", (main, node, loc, name) -> handleByOverapproximation(main, node, loc, name,
				4, new CPrimitive(CPrimitives.LONG))));

		// https://pubs.opengroup.org/onlinepubs/009604499/functions/inet_addr.html
		result.add(new FunctionModel("inet_addr", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPrimitive(CPrimitives.UINT))));

		// https://pubs.opengroup.org/onlinepubs/009604499/functions/close.html
		result.add(new FunctionModel("close", (main, node, loc, name) -> handleByOverapproximation(main, node, loc,
				name, 1, new CPrimitive(CPrimitives.INT))));

		return result;
	}

	@Override
	public Collection<String> getUnsupportedFunctions() {
		return List.of();
	}

}
