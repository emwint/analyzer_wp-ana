 #include <stdlib.h>

int f() {
    int x = 0;
    int i = 0;

    i = i + 1;
    return  i + x;
}


int main() {
    int a = f();
    return a;
}

//git diff --cached --name-only --diff-filter=ACM | grep -E '\.(ml|mli)$' | xargs -I {} ocp-indent -i {}