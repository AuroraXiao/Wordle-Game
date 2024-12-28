import java.util.Scanner;

/**
 *
 * @author Aurora
 */
public class WordleGameCLI {
    
    // Are initialized only once at start of execution
    private static WordleModel model = new WordleModel();
    private static Scanner input = new Scanner(System.in);
    private static String guess;
    // Below used to display colored guess word in Console
    private static final String ANSI_RESET = "\u001B[0m";
    private static final String ANSI_GREY_BACKGROUND = "\u001B[100m";
    private static final String ANSI_GREEN_BACKGROUND = "\u001B[42m";
    private static final String ANSI_YELLOW_BACKGROUND = "\u001B[43m";

    //@ requires \fresh(model);
    //@ requires \fresh(input);
    //@ ensures model != null && input != null;
    public static void main(String[] args) {
        System.out.println(getFormatLogString(
                "--------------------- WORDLE CLI VERSION ------------------------\n"+
                " __          __           _ _         _____                       \n" +
                " \\ \\        / /          | | |       / ____|                      \n" +
                "  \\ \\  /\\  / /__  _ __ __| | | ___  | |  __  __ _ _ __ ___   ___  \n" +
                "   \\ \\/  \\/ / _ \\| '__/ _` | |/ _ \\ | | |_ |/ _` | '_ ` _ \\ / _ \\ \n" +
                "    \\  /\\  / (_) | | | (_| | |  __/ | |__| | (_| | | | | | |  __/ \n" +
                "     \\/  \\/ \\___/|_|  \\__,_|_|\\___|  \\_____|\\__,_|_| |_| |_|\\___| \n" +
                "\n" +
                "-----------------------------------------------------------------",32,1));
        System.out.format (
                "|You have to guess the hidden five-letter word in 6 tries and the|\n" +
                "|color of the letters changes to show how close you are.         |\n"+
                "|Green = Letter is in the word and in the correct spot.          |\n"+
                "|Yellow = Letter is in the word but in the wrong spot.           |\n"+
                "|Grey = Letter isn't in the target word at all.                  |\n",
                model.MAX_GUESSWORD_LENGTH,model.MAX_GUESS_TIMES);
        if (model.alwaysShowAnswer())
                System.out.println("Answer = "+ model.getAnswer() +
                        " - FOR TESTING PURPOSES");
        System.out.println("-".repeat(65));

        while (model.getCurrentGuessTimes() < model.MAX_GUESS_TIMES){
            printAvailableLetters();

            System.out.print(getFormatLogString("Enter Your Guess Word: ",33,1));
            guess = input.nextLine().toLowerCase();
            if (guess.length() != model.MAX_GUESSWORD_LENGTH){
                System.out.print(getFormatLogString("[Warning]:",31,1));
                System.out.format("Enter %d Letters!\n",model.MAX_GUESSWORD_LENGTH);
                continue;
            }
            model.setGuessWord(guess);
            model.submitGuess(); // clears model.guess

            if (model.isWordNotInList()){
                System.out.print(getFormatLogString("[Warning]:",31,1));
                 System.out.println("Word is not in WordList😵!");
                 continue;
            }
            if (model.hasPlayerWon()){
                break;
            }
            printColoredGuess(guess);
            System.out.println("\nTries Left: " +
                    (model.MAX_GUESS_TIMES - model.getCurrentGuessTimes()));
        }
        
        if (model.hasPlayerWon()) {
            System.out.println(getFormatLogString("You win👍! Congratulation🎉!\n",33,1));
            System.out.println(
                    "__   _______ _   _   _    _ _____ _   _ \n" +
                            "\\ \\ / /  _  | | | | | |  | |_   _| \\ | |\n" +
                            " \\ V /| | | | | | | | |  | | | | |  \\| |\n" +
                            "  \\ / | | | | | | | | |/\\| | | | | . ` |\n" +
                            "  | | \\ \\_/ / |_| | \\  /\\  /_| |_| |\\  |\n" +
                            "  \\_/  \\___/ \\___/   \\/  \\/ \\___/\\_| \\_/\n" +
                            "                                        \n");
        }else
           System.out.println(
                   "You lost😥...It's a pity...\n"+
                   "__   _______ _   _   _     _____ _____ _____ \n" +
                   "\\ \\ / /  _  | | | | | |   |  _  /  ___|_   _|\n" +
                   " \\ V /| | | | | | | | |   | | | \\ `--.  | |  \n" +
                   "  \\ / | | | | | | | | |   | | | |`--. \\ | |  \n" +
                   "  | | \\ \\_/ / |_| | | |___\\ \\_/ /\\__/ / | |  \n" +
                   "  \\_/  \\___/ \\___/  \\_____/\\___/\\____/  \\_/  \n" +
                   "                                             \n");
        System.out.print(getFormatLogString("ANSWER = ",33,1));
        System.out.println(ANSI_GREEN_BACKGROUND +
                model.getAnswer().toUpperCase()+ ANSI_RESET);
    }

    //@ requires guess != null;
    //@ ensures true; // no post-condition
    public static void printColoredGuess(String guess){
        for (int i = 0; i < model.MAX_GUESSWORD_LENGTH; i++){
            int COLOR_STATE = model.getGuessStateColor(i); 
            String COLOR = getANSIColorByState(COLOR_STATE);
            System.out.print(COLOR + guess.toUpperCase().charAt(i) + ANSI_RESET);
        }
    }
    
    public static String getANSIColorByState(int COLOR_STATE){
        //@ requires COLOR_STATE == model.GREEN_STATE || COLOR_STATE == model.YELLOW_STATE || COLOR_STATE == model.GREY_STATE;
        //@ ensures \result != null;
        if (COLOR_STATE == model.GREEN_STATE)
            return ANSI_GREEN_BACKGROUND;
        else if (COLOR_STATE == model.YELLOW_STATE)
            return ANSI_YELLOW_BACKGROUND;
        else
            return ANSI_GREY_BACKGROUND;
    }
    
    public static void printAvailableLetters(){
        //@ ensures true; // no post-condition
        String labels[] = {"Green","Yellow","Grey","Available"};
        int states[] = {model.GREEN_STATE,model.YELLOW_STATE,
            model.GREY_STATE,model.NO_STATE};
        String letter;
        int COLOR_STATE;
        System.out.println("------------------------Current Status---------------------------");
        for (int i = 0; i < states.length; i++){
            //@ loop_invariant i >= 0 && i <= states.length;
            //@ loop_variant states.length - i;
            System.out.print(labels[i]+"- ");
            for (Character key : model.getAvailableLetters().keySet()) {
                //@ loop_invariant model.getAvailableLetters().keySet().containsAll(\old(model.getAvailableLetters().keySet()));
                //@ loop_variant model.getAvailableLetters().keySet().size();
                letter = key.toString().toUpperCase();
                COLOR_STATE = model.getAvailableLetters().get(key);
                if (COLOR_STATE == states[i])
                    System.out.print(letter);
            }
            System.out.println();
        }
    }
    public static void printAvailableLettersWithColor(){
        //@ ensures true; // no post-condition
        String letter;
        int COLOR_STATE;
        for (Character key : model.getAvailableLetters().keySet()) {
            //@ loop_invariant model.getAvailableLetters().keySet().containsAll(\old(model.getAvailableLetters().keySet()));
            //@ loop_variant model.getAvailableLetters().keySet().size();
            letter = key.toString().toUpperCase();
            COLOR_STATE = model.getAvailableLetters().get(key);
            if (COLOR_STATE == model.NO_STATE)
                System.out.print(letter);
            else{
                String COLOR = getANSIColorByState(COLOR_STATE);
                System.out.print(COLOR+letter+ ANSI_RESET);
            }
        }
        System.out.println();
    }

    /**
     * @param colour  Colour code: background colour code (41-46); foreground colour code (31-36)
     * @param type    Style codes: 0 none; 1 bold; 3 italic; 4 underline
     * @param content Content to be printed
     */
    private static String getFormatLogString(String content, int colour, int type) {
        boolean hasType = type != 1 && type != 3 && type != 4;
        if (hasType) {
            return String.format("\033[%dm%s\033[0m", colour, content);
        } else {
            return String.format("\033[%d;%dm%s\033[0m", colour, type, content);
        }
    }
}

