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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;

/**
 * Functions from socket.h (see https://pubs.opengroup.org/onlinepubs/009604499/basedefs/sys/socket.h.html). We simply
 * overapproximate the return values of these functions.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class SocketLibraryModel implements ILibraryModel {
	private final FunctionModelHelper mHelper;

	public SocketLibraryModel(final FunctionModelHelper helper) {
		mHelper = helper;
	}

	@Override
	public Collection<FunctionModel> getFunctionModels() {
		final List<FunctionModel> result = new ArrayList<>();

		// https://pubs.opengroup.org/onlinepubs/009604499/functions/accept.html
		result.add(new FunctionModel("accept", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/bind.html
		result.add(new FunctionModel("bind", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/connect.html
		result.add(new FunctionModel("connect", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/listen.html
		result.add(new FunctionModel("listen", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 2, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/socket.html
		result.add(new FunctionModel("socket", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 3, new CPrimitive(CPrimitives.INT))));
		// https://pubs.opengroup.org/onlinepubs/009604499/functions/recv.html
		result.add(new FunctionModel("recv", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 4, new CPrimitive(CPrimitives.LONG))));

		// https://pubs.opengroup.org/onlinepubs/009604499/functions/inet_addr.html
		result.add(new FunctionModel("inet_addr", (main, node, loc, name) -> mHelper.handleByOverapproximation(main,
				node, loc, name, 1, new CPrimitive(CPrimitives.UINT))));

		// https://pubs.opengroup.org/onlinepubs/009604499/functions/close.html
		result.add(new FunctionModel("close", (main, node, loc, name) -> mHelper.handleByOverapproximation(main, node,
				loc, name, 1, new CPrimitive(CPrimitives.INT))));

		return result;
	}
}
