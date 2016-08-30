/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svcomp.chandler;

import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;

import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.TypesResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * TypeHandler for SVComp -- supposed to deal with GNU C specific stuff like builtin types and so..
 * @author nutz
 *
 */
public class SVCompTypeHandler extends TypeHandler {
	
    public SVCompTypeHandler(boolean useIntForAllIntegerTypes) {
		super(useIntForAllIntegerTypes);
	}

	@Override
    public Result visit(Dispatcher main, IASTNamedTypeSpecifier node) {
        final ILocation loc = LocationFactory.createCLocation(node);
        if (node instanceof CASTTypedefNameSpecifier) {
            node = node;
            final String cId = node.getName().toString();
            
            // quick solution --> TODO: maybe make this dependent on includes, 
            // maybe be more elegant (make an entry to symboltable, make a typedef in boogie file??)
            if (cId.equals("size_t") || cId.equals("ssize_t")) {
                return (new TypesResult(new PrimitiveType(loc, SFO.REAL), node.isConst(),
                		false, new CPrimitive(CPrimitives.UINT)));
            } else if (cId.equals("__builtin_va_list")) {
                return (new TypesResult(super.constructPointerType(loc), node.isConst(),
                		false, new CPointer(new CPrimitive(CPrimitives.CHAR))));
            } else if (cId.equals("__pthread_list_t")) {
            	    return (new TypesResult(super.constructPointerType(loc), node.isConst(),
                		false, new CPointer(new CPrimitive(CPrimitives.VOID))));
            } else {
            	return super.visit(main, node);
            }
        }
        final String msg = "Unknown or unsupported type! " + node.toString();
        throw new UnsupportedSyntaxException(loc, msg);
    }
}
