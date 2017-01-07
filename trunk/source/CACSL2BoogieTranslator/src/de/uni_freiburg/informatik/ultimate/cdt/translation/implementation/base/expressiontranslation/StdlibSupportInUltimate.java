/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * Auxiliary file that contains information about stdlib.h and string.h
 * support in ultimate.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class StdlibSupportInUltimate {
	//@formatter:off
	
	private final static String[] SUPPORTED_STD_OPERATIONS_ARRAY = new String[] {
			// functions from stdlib.h
			"malloc",
			"calloc",
			"free",
			"abort",
			
			// functions from string.h
			"memcpy",
			"memset",
			"strlen",
			"strcmp",
	};
	
	private final static String[] UNSUPPORTED_STD_OPERATIONS_ARRAY = new String[] {
			// functions from stdlib.h
			"__ctype_get_mb_cur_max",
			"atof",
			"atoi",
			"atol",
			"atoll",
			"strtod",
			"strtof",
			"strtold",
			"strtol",
			"strtoul",
			"strtoq",
			"strtouq",
			"strtoll",
			"strtoull",
			"l64a",
			"a64l",
			"select",
			"pselect",
			"gnu_dev_major",
			"gnu_dev_minor",
			"gnu_dev_makedev",
			"random",
			"srandom",
			"initstate",
			"setstate",
			"random_r",
			"srandom_r",
			"initstate_r",
			"setstate_r",
			"rand",
			"srand",
			"rand_r",
			"drand48",
			"erand48",
			"lrand48",
			"nrand48",
			"mrand48",
			"jrand48",
			"srand48",
			"seed48",
			"lcong48",
			"drand48_r",
			"erand48_r",
			"lrand48_r",
			"nrand48_r",
			"mrand48_r",
			"jrand48_r",
			"srand48_r",
			"seed48_r",
			"lcong48_r",
			"realloc",
			"cfree",
			"alloca",
			"valloc",
			"posix_memalign",
			"atexit",
			"on_exit",
			"exit",
			"_Exit",
			"getenv",
			"putenv",
			"setenv",
			"unsetenv",
			"clearenv",
			"mktemp",
			"mkstemp",
			"mkstemps",
			"mkdtemp",
			"system",
			"realpath",
			"bsearch",
			"qsort",
			"abs",
			"labs",
			"llabs",
			"div",
			"ldiv",
			"lldiv",
			"ecvt",
			"fcvt",
			"gcvt",
			"qecvt",
			"qfcvt",
			"qgcvt",
			"ecvt_r",
			"fcvt_r",
			"qecvt_r",
			"qfcvt_r",
			"mblen",
			"mbtowc",
			"wctomb",
			"mbstowcs",
			"wcstombs",
			"rpmatch",
			"getsubopt",
			"getloadavg",
			
			
			// functions from string.h

			"memmove",
			"memccpy",
			"memcmp",
			"memchr",
			"strcpy",
			"strncpy",
			"strcat",
			"strncat",
			"strncmp",
			"strcoll",
			"strxfrm",
			"strcoll_l",
			"strxfrm_l",
			"strdup",
			"strndup",
			"strchr",
			"strrchr",
			"strcspn",
			"strspn",
			"strpbrk",
			"strstr",
			"strtok",
			"__strtok_r",
			"strtok_r",
			"strnlen",
			"strerror",
			"strerror_r",
			"strerror_l",
			"__bzero",
			"bcopy",
			"bzero",
			"bcmp",
			"index",
			"rindex",
			"ffs",
			"strcasecmp",
			"strncasecmp",
			"strsep",
			"strsignal",
			"__stpcpy",
			"stpcpy",
			"__stpncpy",
			"stpncpy",
	};
	//@formatter:on

	private final static Set<String> SUPPORTED_STD_OPERATIONS = new HashSet<>(Arrays.asList(SUPPORTED_STD_OPERATIONS_ARRAY));
	
	private final static Set<String> UNSUPPORTED_STD_OPERATIONS = new HashSet<>(Arrays.asList(UNSUPPORTED_STD_OPERATIONS_ARRAY));

	
	
	public static Set<String> getUnsupportedFloatOperations() {
		return UNSUPPORTED_STD_OPERATIONS;
	}
	public static Set<String> getSupportedFloatOperations() {
		return SUPPORTED_STD_OPERATIONS;
	}
	
	

	

}
