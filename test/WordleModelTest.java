import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import static org.junit.Assert.*;

/**
 *
 * @author Ajmal
 */
public class WordleModelTest {
    
    public WordleModelTest() {
    }
    
    @BeforeClass
    public static void setUpClass() {
    }
    
    @AfterClass
    public static void tearDownClass() {
    }
    
    @Before
    public void setUp() {
    }
    
    @After
    public void tearDown() {
    }

    @Test
    public void testInitGame() {
        System.out.println("Testing initGame");
        WordleModel instance = new WordleModel();
        instance.initGame();

        System.out.println("\tAlways Show Answer: " + instance.alwaysShowAnswer());
        System.out.println("\tOnly Word List Guesses: " + instance.onlyWordListGuesses());
        System.out.println("\tIs Guess Submitted: " + instance.isGuessSubmitted());
        System.out.println("\tDisplay Answer: " + instance.displayAnwser());
        System.out.println("\tHas Player Won: " + instance.hasPlayerWon());
        System.out.println("\tAllow New Game: " + instance.allowNewGame());
        System.out.println("\tHas New Game Started: " + instance.hasNewGameStarted());
        System.out.println("\tIs Word Not in List: " + instance.isWordNotInList());
        System.out.println("\tIs Show Answer: " + instance.isShowAnswer());
        System.out.println("\tAnswer: " + instance.getAnswer());
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        System.out.println("\tCurrent Guess Times: " + instance.getCurrentGuessTimes());
        System.out.println("\tAvailable Letters: " + instance.getAvailableLetters());

        assertFalse(instance.alwaysShowAnswer());
        assertTrue(instance.onlyWordListGuesses());
        assertFalse(instance.isGuessSubmitted());
        assertFalse(instance.displayAnwser());
        assertFalse(instance.hasPlayerWon());
        assertFalse(instance.allowNewGame());
        assertFalse(instance.hasNewGameStarted());
        assertFalse(instance.isWordNotInList());
        assertFalse(instance.isShowAnswer());
        assertNotNull(instance.getAnswer());
        assertNotNull(instance.getGuessWord());
        assertEquals(0, instance.getCurrentGuessTimes());
        assertNotNull(instance.getAvailableLetters());
    }


    @Test
    public void testAddToGuess() {
        System.out.println("Testing addToGuess");
        String keyText = "S";
        WordleModel instance = new WordleModel();
        System.out.println("\tGuess Word before add: " + instance.getGuessWord());
        instance.addToGuess(keyText);
        System.out.println("\tGuess Word after add: " + instance.getGuessWord());
        assertEquals(instance.getGuessWord(), "s");
        assertTrue(instance.invariant());
    }

    /**
     * Test of removeFromGuess method, of class WModel.
     * The guess should only have the last character popped off
     * It should also contain no less than 0,
     * or no more than the maximum guess length
     * And should still be within Alphabet.
     */
    @Test
    public void testRemoveFromGuess() {
        System.out.println("Testing removeFromGuess");
        WordleModel instance = new WordleModel();
        instance.setGuessWord("appl");
        System.out.println("\tGuess Word before remove: " + instance.getGuessWord());
        instance.removeFromGuess();
        System.out.println("\tGuess Word after Remove: " + instance.getGuessWord());
        assertEquals(instance.getGuessWord().length() >= 0, true);
        assertEquals(instance.getGuessWord(),"app");
        assertTrue(instance.invariant());
    }
    

    /**
     * Test of submitGuess method, of class WModel.
     * Verify if player has won.
     * Current Guess should be cleared
     * Still Allows for a new game to be started
     * Guess does not have to be inside the word list
     */
    @Test
    public void testSubmitGuess1() {
        System.out.println("Testing submitGuess1");
        WordleModel instance = new WordleModel();
        instance.setGuessWord(instance.getAnswer());
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        instance.submitGuess();
        System.out.println("\tCurrent Guess Times: " + instance.getCurrentGuessTimes());
        assertEquals(instance.getCurrentGuessTimes(),1);
        assertEquals(instance.getGuessWord().length(),0);
        assertTrue(instance.allowNewGame());
        assertTrue(instance.hasPlayerWon());
        assertTrue(instance.onlyWordListGuesses());
    }

    @Test
    public void testSubmitGuess2() {
        System.out.println("Testing submitGuess2");
        WordleModel instance = new WordleModel();
        instance.setGuessWord("hello");
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        // Test when guess is not in word list
        instance.setOnlyAllowWordListGuesses(true);
        instance.submitGuess();
        System.out.println("\tIs Word Not in List: " + instance.isWordNotInList());
        assertFalse(instance.isWordNotInList());
        assertFalse(instance.hasPlayerWon());

        // Test when guess is in word list
        instance.setGuessWord(instance.getAnswer());
        instance.setOnlyAllowWordListGuesses(true);
        instance.submitGuess();
        System.out.println("\tHas Player Won: " + instance.hasPlayerWon());
        assertTrue(instance.hasPlayerWon());
        assertTrue(instance.allowNewGame());
        assertTrue(instance.onlyWordListGuesses());

        // Test when maximum guess times reached
        instance.initGame();
        instance.setGuessWord("\ttest");
        instance.setOnlyAllowWordListGuesses(true);
        for (int i = 1; i < WordleModel.MAX_GUESS_TIMES; i++) {
            instance.submitGuess();
            assertFalse(instance.hasPlayerWon());
            assertFalse(instance.displayAnwser());
        }
        instance.submitGuess();
        System.out.println("\tDisplay Answer: " + instance.displayAnwser());
        assertFalse(instance.displayAnwser());
        assertFalse(instance.hasPlayerWon());
    }
    /**
     * Test of submitGuess method, of class WModel.
     * Verify if game displays answer when player is out of tries.
     * Current Guess should be cleared
     * Allows for a new game to be started
     * Guess has to be inside the word list
     *
     */
    @Test
    public void testSubmitGuess3() {
        System.out.println("Testing submitGuess3");
        WordleModel instance = new WordleModel();
        instance.setGuessWord("hello");
        instance.setOnlyAllowWordListGuesses(true);
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        instance.submitGuess();
        System.out.println("\tCurrent Guess Times: " + instance.getCurrentGuessTimes());
        assertEquals(instance.getCurrentGuessTimes(),1);
        assertEquals(instance.getGuessWord().length(),0);
        assertTrue(instance.allowNewGame());
        assertTrue(instance.onlyWordListGuesses());
        assertFalse(instance.isWordNotInList());
    }

    /**
     * Test of submitGuess method, of class WModel.
     * Verify if player has won.
     * Current Guess should be cleared
     * Still Allows for a new game to be started
     * Guess has to be inside the word list
     */
    @Test
    public void testSubmitGuess4() {
        System.out.println("Testing submitGuess4");
        WordleModel instance = new WordleModel();
        instance.setGuessWord(instance.getAnswer());
        instance.setOnlyAllowWordListGuesses(true);
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        instance.submitGuess();
        System.out.println("\tCurrent Guess Times: " + instance.getCurrentGuessTimes());
        assertEquals(instance.getCurrentGuessTimes(),1);
        assertEquals(instance.getGuessWord().length(),0);
        assertTrue(instance.allowNewGame());
        assertTrue(instance.hasPlayerWon());
        assertTrue(instance.onlyWordListGuesses());
        assertFalse(instance.isWordNotInList());
    }
    

    /**
     * Test of submitGuess method, of class WModel.
     *
     * Guess has to be inside the word list
     * But guess is not inside it
     * 
     */
    @Test
    public void testSubmitGuess5() {
        System.out.println("Testing submitGuess5");
        WordleModel instance = new WordleModel();
        instance.setGuessWord("aPple");
        System.out.println("\tGuess Word: " + instance.getGuessWord());
        instance.setOnlyAllowWordListGuesses(true);
        
        instance.submitGuess();
        assertTrue(instance.onlyWordListGuesses());
        assertTrue(instance.isWordNotInList());
    }

}
