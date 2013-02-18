/**
 * A map for tokens
 * 
 * @author bisser
 * @version 0.0.1
 * @since 308
 * 
 * $LastChangedRevision$
 * $LastChangedDate$
 * $LastChangedBy$
 */

package de.uni_freiburg.informatik.ultimate.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public final class TokenMap extends HashMap<String, String> {

    /**
     * a random serial number
     */
    private static final long serialVersionUID = 7461266221194915552L;
    
    /**
     * a list with all tokens defined by Ultimate
     */
    private static final List<String> m_UNIVERSAL_TOKENS = new ArrayList<String>();
    
    /**
     * default constructor
     */
    public TokenMap() {
        super();
    }
    
    /**
     * initializer for all allowed tokens
     */
    static {
    	for(UniversalTokens ut : UniversalTokens.values())
    	{
    		m_UNIVERSAL_TOKENS.add(ut.toString());
    	}
    }
    
    /**
     * gets a List with all standard tokens defined by Ultimate
     * @return the List
     */
    public static List<String> getUniversalTokens() {
        return m_UNIVERSAL_TOKENS;
    }
    
    /**
     * put a new token in the list, puts null in list for unknown Ultimate tokens
     * @param key the token of the parser
     * @param value the Ultimate token
     * @return the old mapping for this key or null if not set or unknown
     */
    //@Override
    public final String put(String key, String value) {
        if(m_UNIVERSAL_TOKENS.contains(value)) {
            return super.put(key, value);
        }
        return null;
    }
    
    /**
     * gives you a Ultimate token for a parser defined token
     * @param key the parser token
     * @return the ultimate token or null if not defined
     */
    public String get(String key) {
        if(super.containsKey(key)) {
            String s = super.get(key);
            return s;
        } else {
            return null;
        }
    }
}
