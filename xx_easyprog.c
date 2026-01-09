 #include <stdlib.h>

int f(int x, int y) {
    int i = 0;

    i = i + 1;
    
    if (x > 0) {
        i = i + 2;
        return i;
    } else {
        i = i + 3;
        return i + x;
    }
}


int main() {
    int a = 0;
    int c = 3;
    int b = f(a, c);
    return b;
}

//git diff --cached --name-only --diff-filter=ACM | grep -E '\.(ml|mli)$' | xargs -I {} ocp-indent -i {}