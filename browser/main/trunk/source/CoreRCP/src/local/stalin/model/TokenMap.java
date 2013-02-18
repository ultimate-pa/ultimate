/**
 * A map for tokens
 * 
 * @author bisser
 * @version 0.0.1
 * @since 308
 * 
 * $LastChangedRevision: 793 $
 * $LastChangedDate: 2008-11-14 15:14:26 +0100 (Fr, 14. Nov 2008) $
 * $LastChangedBy: dietsch $
 */

package local.stalin.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public final class TokenMap extends HashMap<String, String> {

    /**
     * a random serial number
     */
    private static final long serialVersionUID = 7461266221194915552L;
    
    /**
     * a list with all tokens defined by Stalin
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
     * gets a List with all standard tokens defined by Stalin
     * @return the List
     */
    public static List<String> getUniversalTokens() {
        return m_UNIVERSAL_TOKENS;
    }
    
    /**
     * put a new token in the list, puts null in list for unknown Stalin tokens
     * @param key the token of the parser
     * @param value the Stalin token
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
     * gives you a Stalin token for a parser defined token
     * @param key the parser token
     * @return the stalin token or null if not defined
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
