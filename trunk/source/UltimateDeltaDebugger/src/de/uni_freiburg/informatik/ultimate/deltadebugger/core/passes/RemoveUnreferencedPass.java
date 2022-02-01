/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes;

import java.util.EnumSet;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassDescription;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref.DeclFlag;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref.ObjFlag;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref.RemoveUnreferencedObjects;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.unref.RemoveUnreferencedDecls;

/**
 * Pass to replace unreferenced things.
 */
public final class RemoveUnreferencedPass {
	// Remove certain thins only
	public static final PassDescription FUNCS = PassDescription
			.builder(ctx -> RemoveUnreferencedObjects.analyze(ctx,
					EnumSet.of(ObjFlag.FUNCDEFS, ObjFlag.PROTOTYPES, ObjFlag.INCLUDE_ACSLCOMMENT,
							ObjFlag.INCLUDE_EMPTY_MACROS)))
			.name("Remove unreferenced function definitions and prototypes").build();

	public static final PassDescription TYPES = PassDescription
			.builder(ctx -> RemoveUnreferencedObjects.analyze(ctx,
					EnumSet.of(ObjFlag.COMPOSITES, ObjFlag.ENUMS, ObjFlag.INCLUDE_EMPTY_MACROS)))
			.name("Remove unreferenced composite types and enums").build();

	public static final PassDescription TYPEDEFS = PassDescription
			.builder(ctx -> RemoveUnreferencedDecls.analyze(ctx,
					EnumSet.of(DeclFlag.TYPEDEFS, DeclFlag.GLOBAL, DeclFlag.LOCAL, DeclFlag.MEMBERS,
							DeclFlag.INCLUDE_EMPTY_MACROS)))
			.name("Remove unreferenced typedefs").build();

	public static final PassDescription VARIABLES = PassDescription
			.builder(ctx -> RemoveUnreferencedDecls.analyze(ctx,
					EnumSet.of(DeclFlag.VARS, DeclFlag.GLOBAL, DeclFlag.LOCAL, DeclFlag.INCLUDE_EMPTY_MACROS)))
			.name("Remove unreferenced variables").build();
	
	// Remove everything
	public static final PassDescription ALL_DECLS = PassDescription.builder(RemoveUnreferencedDecls::analyze)
			.name("Remove unreferenced typedefs, variables and composite type members").build();

	public static final PassDescription ALL_OBJS = PassDescription.builder(RemoveUnreferencedObjects::analyze)
			.name("Remove unreferenced funcs, structs, unions and enums").build();

	
	private RemoveUnreferencedPass() {
		
	}
}
