/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
/**
 * Result for initializer lists. E.g. for arrays and structs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Markus Lindenmann
 * @date 04.08.2012
 */
public class ExpressionListRecResult extends ExpressionResult {
    /**
     * The list holding the single elements.
     */
    public final ArrayList<ExpressionListRecResult> list;
    /**
     * The name of this field, for designated initializers.
     */
    public final String field;

    /**
     * Constructor.
     */
    public ExpressionListRecResult() {
        this(null);
    }

    /**
     * Constructor.
     * 
     * @param field
     *            the name of the field e.g. in designated initializers.
     */
    public ExpressionListRecResult(String field) {
        super(null, new LinkedHashMap<VariableDeclaration, ILocation>(0));
        this.field = field;
        list = new ArrayList<ExpressionListRecResult>();
    }

    /**
     * Constructor.
     * 
     * @param stmt
     *            the statement list to hold.
     * @param lrVal
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ExpressionListRecResult(ArrayList<Statement> stmt, LRValue lrVal,
            ArrayList<Declaration> decl, 
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overappr) {
        this(null, stmt, lrVal, decl, auxVars, overappr);
    }

    /**
     * Constructor.
     * 
     * @param field
     *            the name of the field e.g. in designated initializers.
     * @param stmt
     *            the statement list to hold.
     * @param lrVal
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ExpressionListRecResult(String field, ArrayList<Statement> stmt,
            LRValue lrVal, ArrayList<Declaration> decl, 
            Map<VariableDeclaration, ILocation> auxVars,
            List<Overapprox> overappr) {
        super(stmt, lrVal, decl, auxVars, overappr);
        this.field = field;
        list = new ArrayList<ExpressionListRecResult>();
    }
    
    
    @Override
    public ExpressionListRecResult switchToRValueIfNecessary(Dispatcher main,
    		MemoryHandler memoryHandler, StructHandler structHandler,
    		ILocation loc) {
    	final ExpressionResult re = super.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
    	
    	final ArrayList<ExpressionListRecResult> newList = new ArrayList<ExpressionListRecResult>();
    	if (list != null) {
    		for (final ExpressionListRecResult innerRerl : list) {
				newList.add(innerRerl.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc));
			}
    	}
    	final ExpressionListRecResult rerl = new ExpressionListRecResult(field,
    	        re.stmt, re.lrVal, re.decl, re.auxVars, re.overappr);
    	rerl.list.addAll(newList);
    	return rerl;
    }
}
