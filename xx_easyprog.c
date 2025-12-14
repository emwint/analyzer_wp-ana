 #include <stdlib.h>

int main() {
    int z = 0;
    int x = 0;
    int y = 0;
    int i = 0;

    i = i + 1;
    i = i + 2;
    i = i + 3;

    x = x + 1;

    if (x > 0) {
        x = y;
    } else {
        x = x + 2;
    }

    z = z + 1;
    return i + x;
}

//git diff --cached --name-only --diff-filter=ACM | grep -E '\.(ml|mli)$' | xargs -I {} ocp-indent -i {}