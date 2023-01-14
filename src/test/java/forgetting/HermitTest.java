package forgetting;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class HermitTest {

    public static void main(String[] args){
        Map<String, Set<Integer>> map = new HashMap<>();
        Set<Integer> adjacent;
        if((adjacent = map.get("a")) == null){
            map.put("a", new HashSet<>());
            adjacent = map.get("a");
        }
        adjacent.add(1);
        adjacent.add((2));
        Set<Integer> adjacent2 = map.get("a");

        for(Integer i: adjacent2){
            System.out.println(i);
        }

    }
}
