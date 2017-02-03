/* $Id$ 
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.localize;


/**
 * LocalizeException is a runtime exception thrown during Localize export. It contains standard
 * error messages mostly related to unexpected and unsupported types or expression.
 *
 * @author jfaber
 *
 */
public class LocalizeException extends RuntimeException {

    public static final String MALFORMED_OPERATOR_APPLICATION = "Malformed operator application: ";
    public static final String UNEXPECTED_PREDICATE = "Unexpected predicate during Localize export: ";
    public static final String PREDICATE_TYPE_NOT_SUPPORTED = "Predicate type not supported by localize export: ";
    public static final String TYPE_NOT_SUPPORTED = "Type not supported by Localize export: ";
    public static final String NESTED_QUANTIFICATION = "Nested quantified expression not supported by localize export!";
    public static final String UNSUPPORTED_QUANTIFICATION = "Unsupported type in quantification";
    public static final String TYPE_NOT_DECLARED = "Type not declared as basic type (in Z type definitions): ";
    public static final String UNEXPECTED_TERM = "Unexpected term in Localize export: ";
    public static final String UNSUPPORTED_TYPE_IN_CONSTANT_DECLARATION = "Unsupported type in constant declaration: ";
    public static final String MALFORMED_NAME = "Usage of reserved Localize strings; do not use 'XXX' and '_' in names: ";
    public static final String UNEXPECTED_EXPRESSION = "Unexcepted expression in Localize export (predicate expected): ";
    public static final String UNKNOWN_FUNCTION_SYMBOL = "Unknown function symbol (function symbol not declared or only used" +
    		" in query): ";
    public static final String MALFORMED_LOCATION = "Error found in location names: ";
    public static final String EXTENSION_LEVEL_NOT_DEFINED = "Extension level not defined: ";
    public static final String WRONG_NULLPOINTER_TYPE = "Null pointer has no or wrong pointer type: ";
    public static final String DECLARATION_ERROR = "Error while parsing declaration: ";
    
    public LocalizeException(String arg0) {
        super(arg0);
    }

    private static final long serialVersionUID = 6701787159526385114L;



    
}
